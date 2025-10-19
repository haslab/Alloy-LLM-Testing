import json
import sys
import re

if len(sys.argv) != 4:
    print("Usage: python analyze.py <results>.json <input cost> <output cost>")
    sys.exit(1)

generated_instances = 3
results = sys.argv[1]
output = results.replace('.json','.tsv')

input_cost = float(sys.argv[2])/1000000
output_cost = float(sys.argv[3])/1000000

import jpype
import jpype.imports

jpype.startJVM(classpath=["alloytools.jar"])

from edu.mit.csail.sdg.parser import CompUtil
from edu.mit.csail.sdg.translator import A4Options, TranslateAlloyToKodkod
from edu.mit.csail.sdg.alloy4 import A4Reporter

with open(results, 'r') as f, open(output, 'w') as out:
    result = {}
    dataset = json.load(f)
    for example in dataset:
        example_results = result.setdefault(example['example'],{})
        print("========================================")
        print(example['example'])
        print("========================================")
        model = example['model']
        print(model)
        print()
        reqs = []
        for req in example['requirements']:
            req_results = example_results.setdefault(req["pred"],{})
            req_results["desc"] = req["description"]
            req_results["input"] = req["input tokens"]
            req_results["output"] = req["output tokens"]
            req_results["erroneous"] = len(req["erroneous"])

            print('/*')
            print(req['description'])
            print('*/')

            # extract generated instances
            generated_instances = re.findall(r"run(?: \w*)? \{(?:.|\n)*?expect [0-1]",req['instances'], re.MULTILINE)
            parsed_instances = []
            scope_instances = []
            previous_instances = []
            oracle_instances = []
            req_results["generated"] = len(generated_instances)

            # build facts with previous requirements
            prev_facts = ""
            for r in reqs:
                prev_facts += f'fact {{{r}}}\n'

            for instance in generated_instances:

                # Check if command is syntactically correct
                alloy_model = model + "\n" + instance 
                try:
                    world = CompUtil.parseEverything_fromString(None,alloy_model)
                except Exception as e:
                    print("// Failed to parse command")
                    print(instance)
                    continue

                parsed_instances.append(instance)

                # Check if instance is executable (has viable scopes and is satisfiable)
                command = world.getAllCommands()[0]
                options = A4Options()
                try:
                    solution = TranslateAlloyToKodkod.execute_command(None, world.getAllReachableSigs(), command, options)
                except Exception as e:
                    print("// Failed to generate instance for command")
                    print(instance)
                    continue
                if not solution.satisfiable():
                    print("// Failed to generate instance for command")
                    print(instance)
                    continue
                scope_instances.append(instance)

                # Check if instance satisfies previous requirements
                alloy_model +="\n" + prev_facts
                world = CompUtil.parseEverything_fromString(None,alloy_model)
                command = world.getAllCommands()[0]
                options = A4Options()
                solution = TranslateAlloyToKodkod.execute_command(A4Reporter(), world.getAllReachableSigs(), command, options)
                if not solution.satisfiable():
                    print("// Failed to satisfy previous requirements")
                    print(instance)
                    continue
                previous_instances.append(instance)

                # Check if instances conforms to requirement oracle
                alloy_model_oracle = alloy_model + f'\nfact {{{req["oracle"]}}}'
                world = CompUtil.parseEverything_fromString(None,alloy_model_oracle)
                command = world.getAllCommands()[0]
                options = A4Options()
                solution = TranslateAlloyToKodkod.execute_command(A4Reporter(), world.getAllReachableSigs(), command, options)
                if command.expects == 1 and not solution.satisfiable():
                    print("// Unexpectedly failed to generate instance for positive instance")
                    print(instance)
                    continue
                elif command.expects == 0 and solution.satisfiable():
                    print("// Unexpectedly generated instance for negative instance")
                    print(instance)
                    continue
                oracle_instances.append(instance)

            req_results["parse"] = len(parsed_instances)
            req_results["scope"] = len(scope_instances)
            req_results["previous"] = len(previous_instances)
            req_results["oracle"] = len(oracle_instances)

            # Check if instances detect erroneous specifications
            alloy_model = model + "\n" + "\n".join(oracle_instances) + "\n" + prev_facts

            count = 0
            total = 0
            for spec in req["erroneous"]:
                alloy_model_erroneous = alloy_model + f'\nfact {{{spec}}}'
                try:
                    world = CompUtil.parseEverything_fromString(None,alloy_model_erroneous)
                except Exception as e:
                    continue
                total += 1
                # fix for empty instance set
                if len(oracle_instances) == 0:
                    count += 1
                    continue
                commands = world.getAllCommands()
                detected_erroneous = False
                for command in commands:
                    options = A4Options()
                    solution = TranslateAlloyToKodkod.execute_command(A4Reporter(), world.getAllReachableSigs(), command, options)
                    if command.expects == 1 and not solution.satisfiable():
                        detected_erroneous = True
                    elif command.expects == 0 and solution.satisfiable():
                        detected_erroneous = True
                if not detected_erroneous:
                    count += 1

            print(f'// Failed to detect {count} erroneous specifications out of {total}')
            req_results["misses"] = count
            req_results["wrong"] = total

            # Save requirement oracle to check next instances
            reqs.append(req['oracle'])


    # Print summary
    print("Requirement\tInput\tOutput\tCost\tTests\tSyntax\tScopes\tPrevious\tValid\t%\tComplete\tWrong\tMisses\t%")
    out.write("Requirement\tInput\tOutput\tCost\tTests\tSyntax\tScopes\tPrevious\tValid\t%\tComplete\tWrong\tMisses\t%\n")
    input_total = 0
    output_total = 0
    tests_total = 0
    syntax_total = 0
    scopes_total = 0
    previous_total = 0
    valid_total = 0
    wrong_total = 0
    misses_total = 0
    average_total = 0
    complete_total = 0
    for example in result:
        input_req = 0
        output_req = 0
        tests_req = 0
        syntax_req = 0
        scopes_req = 0
        previous_req = 0
        valid_req = 0
        wrong_req = 0
        misses_req = 0
        average_req = 0
        complete_req = 0
        for req in result[example]:
            current = result[example][req]
            print(f'{current["desc"]}\t{current["input"]}\t{current["output"]}\t{current["input"]*input_cost+current["output"]*output_cost:.2f}\t{current["generated"]}\t{current["parse"]}\t{current["scope"]}\t{current["previous"]}\t{current["oracle"]}\t{(current["oracle"]/current["generated"])*100:.2f}', end='')
            out.write(f'{current["desc"]}\t{current["input"]}\t{current["output"]}\t{current["input"]*input_cost+current["output"]*output_cost:.2f}\t{current["generated"]}\t{current["parse"]}\t{current["scope"]}\t{current["previous"]}\t{current["oracle"]}\t{(current["oracle"]/current["generated"])*100:.2f}')
            input_req += current["input"]
            output_req += current["output"]
            tests_req += current["generated"]
            syntax_req += current["parse"]
            scopes_req += current["scope"]
            previous_req += current["previous"]
            valid_req += current["oracle"]
            if current["oracle"] == current["generated"]:
                print(f'\t1\t{current["wrong"]}\t{current["misses"]}\t{(current["misses"]/current["wrong"])*100:.2f}')
                out.write(f'\t1\t{current["wrong"]}\t{current["misses"]}\t{(current["misses"]/current["wrong"])*100:.2f}\n')
                wrong_req += current["wrong"]
                misses_req += current["misses"]
                complete_req += 1
                average_req += (current["misses"]/current["wrong"])*100
            else:
                print("\t0\t\t\t")
                out.write("\t0\t\t\t\n")
        print(f'{example} totals\t{input_req}\t{output_req}\t{input_req*input_cost+output_req*output_cost:.2f}\t{tests_req}\t{syntax_req}\t{scopes_req}\t{previous_req}\t{valid_req}\t{(valid_req/tests_req)*100:.1f}\t{complete_req}\t{wrong_req}\t{misses_req}\t{(average_req/complete_req) if complete_req > 0 else 0:.2f}')
        out.write(f'**{example} totals**\t**{input_req}**\t**{output_req}**\t**{input_req*input_cost+output_req*output_cost:.2f}**\t**{tests_req}**\t**{syntax_req}**\t**{scopes_req}**\t**{previous_req}**\t**{valid_req}**\t**{(valid_req/tests_req)*100:.1f}**\t**{complete_req}**\t**{wrong_req}**\t**{misses_req}**\t**{(average_req/complete_req) if complete_req > 0 else 0:.2f}**\n')
        input_total += input_req
        output_total += output_req
        tests_total += tests_req
        syntax_total += syntax_req
        scopes_total += scopes_req
        previous_total += previous_req
        valid_total += valid_req
        wrong_total += wrong_req
        misses_total += misses_req
        complete_total += complete_req
        average_total += average_req
    print(f'Totals\t{input_total}\t{output_total}\t{input_total*input_cost+output_total*output_cost:.2f}\t{tests_total}\t{syntax_total}\t{scopes_total}\t{previous_total}\t{valid_total}\t{(valid_total/tests_total)*100:.2f}\t{complete_total}\t{wrong_total}\t{misses_total}\t{(average_total/complete_total) if complete_total > 0 else 0:.2f}')
    out.write(f'**Totals**\t**{input_total}**\t**{output_total}**\t**{input_total*input_cost+output_total*output_cost:.2f}**\t**{tests_total}**\t**{syntax_total}**\t**{scopes_total}**\t**{previous_total}**\t**{valid_total}**\t**{(valid_total/tests_total)*100:.2f}**\t**{complete_total}**\t**{wrong_total}**\t**{misses_total}**\t**{(average_total/complete_total) if complete_total > 0 else 0:.2f}**\n')

# Claude generated function to convert tsv to markdown
def tsv_to_markdown(input_file, output_file=None):
    """
    Convert a tab-separated values file to GitHub Markdown table format.
    
    Args:
        input_file: Path to the TSV file
        output_file: Optional path to save the markdown table (if None, prints to console)
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

tsv_to_markdown(output, output.replace('.tsv','.md'))
import os
os.remove(output)
