import json
import os
import re
import argparse
import sys

if __package__:
    from .definitions import DefinitionChecker
    from .suite_metadata import complete_suite, requested_n
else:
    from definitions import DefinitionChecker
    from suite_metadata import complete_suite, requested_n


REPAIR_CALLS_NOTE = (
    "**Repair calls:** additional corrective LLM requests after the initial response. "
    "A batched request counts once, including unsuccessful repairs. "
    "`0` means repair handling was enabled but no corrective request was made; "
    "`—` means repairs were disabled or repair metadata is unavailable. "
    "Subtotals and totals are `—` if any included requirement is untracked. "
    "Token and cost totals include recorded repair calls. API/network retries are excluded."
)

DEFINITION_NOTE = (
    "**Defined:** consistent tests whose satisfying instances are unique modulo atom renaming "
    "under the declarations and the command's original scopes and integer bitwidth. "
    "A complete concrete encoding certifies uniqueness directly; otherwise the first solution "
    "is encoded as a complete instance predicate I and Alloy checks whether the original test "
    "P admits a solution satisfying P and not I. All user-declared signatures and fields, "
    "including ordering successors, are compared; private module implementation relations "
    "and Skolem witnesses are excluded. The target requirement is not imposed during this "
    "check, so negative scenarios remain satisfiable. Tests with non-isomorphic satisfying "
    "instances are excluded from later validity, completeness, and coverage checks."
)


def repair_call_count(requirement):
    """Count recorded corrective requests, excluding the initial generation."""
    states = [requirement[key] for key in ("syntax repair", "json repair") if key in requirement]
    if not states or any(not isinstance(state, dict) or not isinstance(state.get("rounds"), list)
                         for state in states):
        return None
    count = sum(len(state["rounds"]) for state in states)
    if count == 0 and all(state.get("max attempts") == 0 for state in states):
        return None
    return count


def repair_call_total(counts):
    """A missing count makes the total unknown, rather than a partial sum."""
    counts = list(counts)
    return sum(counts) if counts and all(count is not None for count in counts) else None


def format_repair_calls(count):
    return "—" if count is None else str(count)


def extract_generated_instances(source):
    """Keep malformed run commands without treating comments as expect clauses."""
    trivia = re.compile(r'"(?:\\.|[^"\\])*"|//[^\n]*|--[^\n]*|/\*[\s\S]*?(?:\*/|$)|^[ \t]*```[^\n]*', re.MULTILINE)
    masked = trivia.sub(lambda match: re.sub(r"[^\n]", " ", match.group()), source)
    starts = [match.start() for match in re.finditer(r"\brun\b", masked)]
    instances = []
    for start, limit in zip(starts, starts[1:] + [len(source)]):
        expectation = re.search(r"\bexpect\s+[01]\b", masked[start:limit])
        end = start + expectation.end() if expectation else len(masked[:limit].rstrip())
        instances.append(source[start:end].strip())
    return instances


def percentage(count, total):
    """An empty population contributes zero rather than dividing by zero."""
    return 100 * count / total if total else 0


def parseArgs():
    parser = argparse.ArgumentParser(description="Script for processing LLM-generated instances")
    sub = parser.add_subparsers(dest="cmd",required=True)

    p_process = sub.add_parser("process", help="process an LLM execution")
    p_process.add_argument("jar", help="AlloyTools jar path")
    p_process.add_argument("results", help="JSON LLM instance generation results")
    p_process.add_argument("icost", type=float, help="input cost")
    p_process.add_argument("ocost", type=float, help="output cost")
    p_process.add_argument("--max-coverage", metavar="RESULTS_JSON",
                           help="optional minimal/run_rates.py results.json for comparison with the optimum")

    p_all = sub.add_parser("all", help="process a set of LLM executions from a JSON file")
    p_all.add_argument("jar", help="AlloyTools jar path")
    p_all.add_argument("execs", help="JSON file reporting a set of LLM executions and costs")
    p_all.add_argument("--max-coverage", metavar="RESULTS_JSON",
                       help="optional minimal/run_rates.py results.json for comparison with the optimum")

    return parser.parse_args()

def main():
    args = parseArgs()
    maximum_coverage = None
    if args.max_coverage:
        if __package__:
            from .max_coverage import CoverageReference, append_comparison_columns, within_scope
        else:
            from max_coverage import CoverageReference, append_comparison_columns, within_scope
        try:
            maximum_coverage = CoverageReference(args.max_coverage)
        except (OSError, ValueError, KeyError) as exc:
            raise SystemExit(f"Invalid maximum-coverage results: {exc}") from exc
    import jpype
    import jpype.imports

    jpype.startJVM(classpath=[args.jar])

    from edu.mit.csail.sdg.parser import CompUtil
    from edu.mit.csail.sdg.translator import A4Options, TranslateAlloyToKodkod
    from edu.mit.csail.sdg.alloy4 import A4Reporter


    if args.cmd == "process":
        benchs = [(args.results,args.icost,args.ocost)]

    else:

        with open(args.execs, 'r') as bench_file:
            benchs_execs = json.load(bench_file)
        benchs = [(os.path.join(os.path.dirname(args.execs), d["results"]),d["icost"],d["ocost"]) for d in benchs_execs]

    for results, icost, ocost in benchs:
        fallback_count, unknown_count = 0, 0
    
        ifile = os.path.basename(results)
        output = ifile.replace('.json','.tsv')
        outputt = ifile.replace('.json','.txt')
        outputf = ifile.replace('.json','_failures.json')

        input_cost = float(icost)/1000000
        output_cost = float(ocost)/1000000

        with open(results, 'r') as f, open(output, 'w') as out, open(outputt, 'w') as outt:
            result = {}
            failures = {}
            dataset = json.load(f)
            for example in dataset:
                example_results = result.setdefault(example['example'],{})
                print("========================================")
                print(example['example'])
                print("========================================")
                model = example['model']
                definitions = DefinitionChecker(CompUtil.parseEverything_fromString(None, model))
                print(model)
                print()
                prev_reqs = []
                for req in example['requirements']:
                    req_results = example_results.setdefault(req["pred"],{})
                    req_results["desc"] = req["description"]
                    req_results["input"] = req["input tokens"]
                    req_results["output"] = req["output tokens"]
                    req_results["repair_calls"] = repair_call_count(req)
                    req_results["erroneous"] = len(req["erroneous"])
                    try:
                        n, used_fallback = requested_n(req, results)
                    except ValueError as exc:
                        raise SystemExit(f"Invalid requested count for {example['example']} {req['pred']}: {exc}") from exc
                    req_results["n"] = n
                    fallback_count += used_fallback
                    unknown_count += n is None

                    print('/*')
                    print(req['description'])
                    print('*/')

                    # extract generated instances
                    generated_instances = extract_generated_instances(req['instances'])
                    parsed_instances, consistent_instances, defined_instances, previous_instances, oracle_instances = [], [], [], [], []
                    positives, negatives, scoped = 0, 0, 0

                    req_results["generated"] = len(generated_instances)

                    # build facts with previous requirements
                    prev_facts = ""
                    for r in prev_reqs:
                        prev_facts += f'fact {{{r}}}\n'

                    for instance in generated_instances:

                        # Check if command is syntactically correct
                        alloy_model = model + "\n" + instance 
                        try:
                            world = CompUtil.parseEverything_fromString(None,alloy_model)
                            command = world.getAllCommands()[0]
                            if command.expects not in (0, 1):
                                raise ValueError("A test must include an expect 0 or expect 1 clause.")
                        except Exception as e:
                            print("// Failed to parse command")
                            print(instance)
                            failures.setdefault(example['example'],{}).setdefault(req["pred"],{}).setdefault("parse", []).append(instance)
                            continue

                        parsed_instances.append(instance)
                        positives += command.expects == 1
                        negatives += command.expects == 0

                        # Check if instance is consistent (has viable scopes and is satisfiable)
                        options = A4Options()
                        try:
                            solution = TranslateAlloyToKodkod.execute_command(None, world.getAllReachableSigs(), command, options)
                        except Exception as e:
                            print("// Failed to generate instance for command")
                            print(instance)
                            failures.setdefault(example['example'],{}).setdefault(req["pred"],{}).setdefault("consistent", []).append(instance)
                            continue
                        if not solution.satisfiable():
                            print("// Failed to generate instance for command")
                            print(instance)
                            failures.setdefault(example['example'],{}).setdefault(req["pred"],{}).setdefault("consistent", []).append(instance)
                            continue
                        consistent_instances.append(instance)

                        if not definitions.unique(world, command, solution, options):
                            print("// Test admits multiple non-isomorphic satisfying instances")
                            print(instance)
                            failures.setdefault(example['example'],{}).setdefault(req["pred"],{}).setdefault("defined", []).append(instance)
                            continue
                        defined_instances.append(instance)

                        # Check if instance satisfies previous requirements
                        alloy_model += "\n" + prev_facts
                        world = CompUtil.parseEverything_fromString(None,alloy_model)
                        command = world.getAllCommands()[0]
                        solution = TranslateAlloyToKodkod.execute_command(A4Reporter(), world.getAllReachableSigs(), command, options)
                        if not solution.satisfiable():
                            print("// Failed to satisfy previous requirements")
                            print(instance)
                            failures.setdefault(example['example'],{}).setdefault(req["pred"],{}).setdefault("previous", []).append(instance)
                            continue
                        previous_instances.append(instance)
                        background_world, background_command, background_solution = world, command, solution

                        # Check if instances conforms to requirement oracle
                        alloy_model_oracle = alloy_model + f'\nfact {{{req["oracle"]}}}'
                        world = CompUtil.parseEverything_fromString(None,alloy_model_oracle)
                        command = world.getAllCommands()[0]
                        solution = TranslateAlloyToKodkod.execute_command(A4Reporter(), world.getAllReachableSigs(), command, options)
                        if command.expects == 1 and not solution.satisfiable():
                            print("// Unexpectedly failed to generate instance for positive instance")
                            print(instance)
                            failures.setdefault(example['example'],{}).setdefault(req["pred"],{}).setdefault("valid", []).append(instance)
                            continue
                        elif command.expects == 0 and solution.satisfiable():
                            print("// Unexpectedly generated instance for negative instance")
                            failures.setdefault(example['example'],{}).setdefault(req["pred"],{}).setdefault("valid", []).append(instance)
                            print(instance)
                            continue
                        oracle_instances.append(instance)
                        if maximum_coverage and within_scope(background_world, background_command, background_solution,
                                                             maximum_coverage.scope, options):
                            scoped += 1

                    req_results["parse"] = len(parsed_instances)
                    req_results["scope"] = len(consistent_instances)
                    req_results["defined"] = len(defined_instances)
                    req_results["previous"] = len(previous_instances)
                    req_results["oracle"] = len(oracle_instances)
                    req_results["complete"] = complete_suite(n, len(generated_instances), positives,
                                                            negatives, len(oracle_instances))

                    # Check if instances detect erroneous specifications
                    alloy_model = model + "\n" + "\n".join(oracle_instances) + "\n" + prev_facts

                    count = 0
                    total = 0
                    for spec in req["erroneous"]:
                        alloy_model_erroneous = alloy_model + f'\nfact {{{spec}}}'
                        try:
                            world = CompUtil.parseEverything_fromString(None,alloy_model_erroneous)
                        except Exception as e:
                            print(f'// Failed to parse erroneous specification: {alloy_model_erroneous}')
                            continue
                        total += 1
                        # fix for empty instance set
                        if len(oracle_instances) == 0:
                            continue
                        commands = world.getAllCommands()
                        detected_erroneous = False
                        for command in commands:
                            solution = TranslateAlloyToKodkod.execute_command(A4Reporter(), world.getAllReachableSigs(), command, options)
                            if (command.expects == 1 and not solution.satisfiable()) or (command.expects == 0 and solution.satisfiable()):
                                detected_erroneous = True
                                break
                        if detected_erroneous:
                            count += 1

                    print(f'// Detected {count} erroneous specifications out of {total}')
                    req_results["detected"] = count
                    req_results["wrong"] = total
                    if maximum_coverage:
                        req_results["max_coverage"] = maximum_coverage.compare(
                            example, req, prev_reqs, req_results, scoped)

                    # Save requirement oracle to check next instances
                    prev_reqs.append(req['oracle'])


            # Print summary
            out.write("Requirement\tn\tInput\tOutput\tCost\tRepair calls\tTests\tSyntax\tConsistent\tDefined\tPrevious\tValid\t%\tComplete\tWrong\tDetected\t% of total\n")
            outt.write("Requirement\tn\tInput\tOutput\tCost\tRepair calls\tTests\tSyntax\tConsistent\tDefined\tPrevious\tValid\t%\tComplete\tWrong\tDetected\t% of total\n")
            input_total = 0
            output_total = 0
            repair_totals = []
            tests_total = 0
            syntax_total = 0
            scopes_total = 0
            defined_total = 0
            previous_total = 0
            valid_total = 0
            wrong_total = 0
            detected_total = 0
            average_total = 0
            complete_total = 0
            for example in result:
                summaries = ((r["input"], r["output"], r["generated"], r["parse"], r["scope"], r["defined"], r["previous"], r["oracle"],
                              r["wrong"] if r["complete"] else 0,
                              r["detected"] if r["complete"] else 0,
                              r["complete"],
                              percentage(r["detected"], r["wrong"]) if r["complete"] else 0) for r in result[example].values())
                input_req, output_req, tests_req, syntax_req, scopes_req, defined_req, previous_req, valid_req, wrong_req, detected_req, complete_req, average_req = map(sum, zip(*summaries))
                repairs_req = repair_call_total(r["repair_calls"] for r in result[example].values())
                repair_totals.append(repairs_req)
                for req in result[example]:
                    current = result[example][req]
                    out.write(f'{current["desc"]}\t{current["n"] if current["n"] is not None else "—"}\t{current["input"]}\t{current["output"]}\t{current["input"]*input_cost+current["output"]*output_cost:.2f}\t{format_repair_calls(current["repair_calls"])}\t{current["generated"]}\t{current["parse"]}\t{current["scope"]}\t{current["defined"]}\t{current["previous"]}\t{current["oracle"]}\t{percentage(current["oracle"], current["generated"]):.2f}')
                    outt.write(f'{current["desc"]}\t{current["n"] if current["n"] is not None else "—"}\t{current["input"]}\t{current["output"]}\t{current["input"]*input_cost+current["output"]*output_cost:.2f}\t{format_repair_calls(current["repair_calls"])}\t{current["generated"]}\t{current["parse"]}\t{current["scope"]}\t{current["defined"]}\t{current["previous"]}\t{current["oracle"]}\t{percentage(current["oracle"], current["generated"]):.2f}')
                    if current["complete"]:
                        out.write(f'\t1\t{current["wrong"]}\t{current["detected"]}\t{percentage(current["detected"], current["wrong"]):.2f}\n')
                        outt.write(f'\t1\t{current["wrong"]}\t{current["detected"]}\t{percentage(current["detected"], current["wrong"]):.2f}\n')
                    else:
                        out.write("\t0\t\t\t\n")
                        outt.write("\t0\t\t\t\n")
                out.write(f'**{example} totals**\t**—**\t**{input_req}**\t**{output_req}**\t**{input_req*input_cost+output_req*output_cost:.2f}**\t**{format_repair_calls(repairs_req)}**\t**{tests_req}**\t**{syntax_req}**\t**{scopes_req}**\t**{defined_req}**\t**{previous_req}**\t**{valid_req}**\t**{percentage(valid_req, tests_req):.1f}**\t**{complete_req}**\t**{wrong_req}**\t**{detected_req}**\t**{(average_req/complete_req) if complete_req > 0 else 0:.2f}**\n')
                outt.write(f'{example} totals\t—\t{input_req}\t{output_req}\t{input_req*input_cost+output_req*output_cost:.2f}\t{format_repair_calls(repairs_req)}\t{tests_req}\t{syntax_req}\t{scopes_req}\t{defined_req}\t{previous_req}\t{valid_req}\t{percentage(valid_req, tests_req):.1f}\t{complete_req}\t{wrong_req}\t{detected_req}\t{(average_req/complete_req) if complete_req > 0 else 0:.2f}\n')
                input_total += input_req
                output_total += output_req
                tests_total += tests_req
                syntax_total += syntax_req
                scopes_total += scopes_req
                defined_total += defined_req
                previous_total += previous_req
                valid_total += valid_req
                wrong_total += wrong_req
                detected_total += detected_req
                complete_total += complete_req
                average_total += average_req
            repairs_total = repair_call_total(repair_totals)
            out.write(f'**Totals**\t**—**\t**{input_total}**\t**{output_total}**\t**{input_total*input_cost+output_total*output_cost:.2f}**\t**{format_repair_calls(repairs_total)}**\t**{tests_total}**\t**{syntax_total}**\t**{scopes_total}**\t**{defined_total}**\t**{previous_total}**\t**{valid_total}**\t**{percentage(valid_total, tests_total):.2f}**\t**{complete_total}**\t**{wrong_total}**\t**{detected_total}**\t**{(average_total/complete_total) if complete_total > 0 else 0:.2f}**\n')
            outt.write(f'Totals\t—\t{input_total}\t{output_total}\t{input_total*input_cost+output_total*output_cost:.2f}\t{format_repair_calls(repairs_total)}\t{tests_total}\t{syntax_total}\t{scopes_total}\t{defined_total}\t{previous_total}\t{valid_total}\t{percentage(valid_total, tests_total):.2f}\t{complete_total}\t{wrong_total}\t{detected_total}\t{(average_total/complete_total) if complete_total > 0 else 0:.2f}\n')

        footer = REPAIR_CALLS_NOTE + "\n\n" + DEFINITION_NOTE
        if fallback_count:
            note = (f"Requested n was inferred from the filename for {fallback_count} requirement(s) "
                    "without recorded counts.")
            print(f"Note: {results}: {note}", file=sys.stderr)
            footer += "\n\n" + note
        if unknown_count:
            note = (f"Requested n could not be determined for {unknown_count} requirement(s); "
                    "their suites cannot be marked complete.")
            print(f"Warning: {results}: {note}", file=sys.stderr)
            footer += "\n\n" + note
        if maximum_coverage:
            append_comparison_columns((output, outputt), result, maximum_coverage.scope)
            footer += "\n\n" + maximum_coverage.footer()
        tsv_to_markdown(output, output.replace('.tsv','.md'), footer=footer)
        os.remove(output)

        with open(outputf, 'w') as outf:
            json.dump(failures, outf, indent=4)

# Claude generated function to convert tsv to markdown
def tsv_to_markdown(input_file, output_file=None, footer=None):
    """
    Convert a tab-separated values file to GitHub Markdown table format.
    
    Args:
        input_file: Path to the TSV file
        output_file: Optional path to save the markdown table (if None, prints to console)
        footer: Optional explanatory text to append below the table
    """
    try:
        with open(input_file, 'r', encoding='utf-8') as f:
            lines = [line.rstrip('\n') for line in f.readlines()]
        
        if not lines:
            print("Error: File is empty")
            return
        
        # Split each line by tabs
        rows = [line.split('\t') for line in lines]
        
        # Calculate column widths for better formatting
        col_widths = []
        if rows:
            num_cols = len(rows[0])
            for col in range(num_cols):
                max_width = max(len(str(row[col])) if col < len(row) else 0 for row in rows)
                col_widths.append(max(max_width, 3))  # Minimum width of 3
        
        # Build markdown table
        markdown_lines = []
        
        for i, row in enumerate(rows):
            # Pad cells to column width
            cells = [str(cell).ljust(col_widths[j]) for j, cell in enumerate(row)]
            markdown_lines.append('| ' + ' | '.join(cells) + ' |')
            
            # Add separator after header row
            if i == 0:
                separators = ['-' * width for width in col_widths]
                markdown_lines.append('| ' + ' | '.join(separators) + ' |')
        
        markdown_table = '\n'.join(markdown_lines)
        if footer:
            markdown_table += '\n\n' + footer + '\n'
        
        # Output results
        if output_file:
            with open(output_file, 'w', encoding='utf-8') as f:
                f.write(markdown_table)
            print(f"Markdown table saved to: {output_file}")
        else:
            print(markdown_table)
        
        return markdown_table
        
    except FileNotFoundError:
        print(f"Error: File '{input_file}' not found")
    except Exception as e:
        print(f"Error: {e}")


if __name__ == "__main__":
    main()
