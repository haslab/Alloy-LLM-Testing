import json
import sys
import re

# check if there is one application parameter
if len(sys.argv) != 2:
    print("Usage: python analyze.py <dataset>")
    sys.exit(1)

generated_instances = 3
dataset = sys.argv[1]

import jpype
import jpype.imports

jpype.startJVM(classpath=["alloytools.jar"])

from edu.mit.csail.sdg.parser import CompUtil
from edu.mit.csail.sdg.translator import A4Options, TranslateAlloyToKodkod
from edu.mit.csail.sdg.alloy4 import A4Reporter

with open(dataset, 'r') as f:
    result = {}
    dataset = json.load(f)
    for example in dataset:
        example_results = result.setdefault(example["id"],{})
        print("========================================")
        print(example['example'])
        print("========================================")
        model = example['model']
        reqs = []
        for req in example['requirements']:
            req_results = example_results.setdefault(req["pred"],{})
            req_results["desc"] = req["description"]
            req_results["input"] = req["input tokens"]
            req_results["output"] = req["output tokens"]
            req_results["erroneous"] = len(req["erroneous"])

            print('> ' + req['description'])
            print(str(req['input tokens']) + ' input tokens used')
            print(str(req['output tokens']) + ' output tokens used')

            # Check syntax (brittle RE)
            generated_instances = re.findall(r"run \w* \{(?:.|\n)*?expect [0-1]",req['instances'], re.MULTILINE)
            parsed_instances = []
            scope_instances = []
            previous_instances = []
            oracle_instances = []
            req_results["generated"] = len(generated_instances)

            prev_facts = ""
            for r in reqs:
                prev_facts += f'fact {{{r}}}\n'

            for instance in generated_instances:
                alloy_model = model + "\n" + instance 
                try:
                    world = CompUtil.parseEverything_fromString(None,alloy_model)
                except Exception as e:
                    print("Failed to parse Alloy model")
                    print(instance)
                    continue

                parsed_instances.append(instance)

                # Check if instances are well formed (can generate exactly one instance without facts)
                command = world.getAllCommands()[0]
                options = A4Options()
                try:
                    solution = TranslateAlloyToKodkod.execute_command(None, world.getAllSigs(), command, options)
                except Exception as e:
                    print("Failed to generate instance for command")
                    print(instance)
                    continue
                if not solution.satisfiable():
                    print("Failed to generate instance for command")
                    print(instance)
                    continue
                """ non determinism checking is not working as expected because of bad symmetry breaking
                solution = solution.next()
                if solution.satisfiable():
                    print("Generated multiple instances for command")
                    print(command)
                    commands_well_formed = False
                """
                
                scope_instances.append(instance)

                # check if instances satisfy previous requirements
                alloy_model +="\n" + prev_facts
                world = CompUtil.parseEverything_fromString(None,alloy_model)
                command = world.getAllCommands()[0]
                options = A4Options()
                solution = TranslateAlloyToKodkod.execute_command(A4Reporter(), world.getAllSigs(), command, options)
                if not solution.satisfiable():
                    print("Instance failed to satisfy previous requirements")
                    print(instance)
                    continue

                previous_instances.append(instance)

                # Check if instances meet expectations
                alloy_model_oracle = alloy_model + f'\nfact {{{req["oracle"]}}}'
                world = CompUtil.parseEverything_fromString(None,alloy_model_oracle)
                command = world.getAllCommands()[0]
                options = A4Options()
                solution = TranslateAlloyToKodkod.execute_command(A4Reporter(), world.getAllSigs(), command, options)
                if command.expects == 1 and not solution.satisfiable():
                    print("Unexpectedly failed to generate instance for positive instance")
                    print(instance)
                    continue
                elif command.expects == 0 and solution.satisfiable():
                    print("Unexpectedly generated instance for negative instance")
                    print(instance)
                    continue

                oracle_instances.append(instance)

            req_results["parse"] = len(parsed_instances)
            req_results["scope"] = len(scope_instances)
            req_results["previous"] = len(previous_instances)
            req_results["oracle"] = len(oracle_instances)

            # check if instances detect erroneous specifications
            alloy_model = model + "\n" + "\n".join(oracle_instances) + "\n" + prev_facts

            count = 0
            total = 0
            for spec in req["erroneous"]:
                alloy_model_erroneous = alloy_model + f'\nfact {{{spec}}}'
                try:
                    world = CompUtil.parseEverything_fromString(None,alloy_model_erroneous)
                except:
                    continue
                total += 1
                commands = world.getAllCommands()
                detected_erroneous = False
                for command in commands:
                    options = A4Options()
                    solution = TranslateAlloyToKodkod.execute_command(A4Reporter(), world.getAllSigs(), command, options)
                    if command.expects == 1 and not solution.satisfiable():
                        detected_erroneous = True
                    elif command.expects == 0 and solution.satisfiable():
                        detected_erroneous = True
                if not detected_erroneous:
                    #print(spec)
                    count += 1
            print(f'Failed to detect {count} erroneous specifications out of {total}')
            req_results["misses"] = count
            req_results["total"] = total


            # save requirement oracle to check next instances
            reqs.append(req['oracle'])


    print("requirement\t#erroneous\tinput\touput\t#generated\t#parsed\t#scope\t#previous\t#valid\t#misses")
    for example in result:
        for req in result[example]:
            current = result[example][req]
            print(f'{current["desc"]}\t{current["total"]}\t{current["input"]}\t{current["output"]}\t{current["generated"]}\t{current["parse"]}\t{current["scope"]}\t{current["previous"]}\t{current["oracle"]}\t{current["misses"]}')
