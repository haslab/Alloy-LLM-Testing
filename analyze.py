import json
import sys

# check if there is one application parameter
if len(sys.argv) != 2:
    print("Usage: python analyze.py <dataset>")
    sys.exit(1)

instances = 3
dataset = sys.argv[1]

import jpype
import jpype.imports

jpype.startJVM(classpath=["alloytools.jar"])

from edu.mit.csail.sdg.parser import CompUtil
from edu.mit.csail.sdg.translator import A4Options, TranslateAlloyToKodkod
from edu.mit.csail.sdg.alloy4 import A4Reporter

with open(dataset+'.json', 'r') as f:
    dataset = json.load(f)
    for example in dataset:
        print("========================================")
        print(example['example'])
        print("========================================")
        model = example['model']
        reqs = []
        for req in example['requirements']:
            print('> ' + req['description'])
            print(str(req['input tokens']) + ' input tokens used')
            print(str(req['output tokens']) + ' output tokens used')

            # Check syntax
            alloy_model = model + "\n" + req['instances']
            try:
                world = CompUtil.parseEverything_fromString(None,alloy_model)
            except:
                print("Failed to parse Alloy model")
                print(alloy_model)
                continue

            # Check if instances are well formed (can generate exactly one instance without facts)
            commands = world.getAllCommands()
            commands_well_formed = True
            for command in commands:
                options = A4Options()
                try:
                    solution = TranslateAlloyToKodkod.execute_command(None, world.getAllSigs(), command, options)
                except:
                    print("Failed to generate instance for command")
                    print(command)
                    commands_well_formed = False
                    continue
                if not solution.satisfiable():
                    print("Failed to generate instance for command")
                    print(command)
                    commands_well_formed = False
                    continue
                """ non determinism checking is not working as expected because of bad symmetry breaking
                solution = solution.next()
                if solution.satisfiable():
                    print("Generated multiple instances for command")
                    print(command)
                    commands_well_formed = False
                """
            if not commands_well_formed:
                print(alloy_model)
                continue

            # check if instances satisfy previous requirements
            facts = ""
            for r in reqs:
                facts += f'fact {{{r}}}\n'
            alloy_model +="\n" + facts
            world = CompUtil.parseEverything_fromString(None,alloy_model)
            commands = world.getAllCommands()
            commands_satisfy_previous = True
            for command in commands:
                options = A4Options()
                solution = TranslateAlloyToKodkod.execute_command(A4Reporter(), world.getAllSigs(), command, options)
                if not solution.satisfiable():
                    print("Instance failed to satisfy previous requirements")
                    print(command)
                    commands_satisfy_previous = False
            if not commands_satisfy_previous:
                print(alloy_model)
                continue

            # Check if instances meet expectations
            alloy_model_oracle = alloy_model + f'\nfact {{{req["oracle"]}}}'
            world = CompUtil.parseEverything_fromString(None,alloy_model_oracle)
            commands = world.getAllCommands()
            commands_as_expected = True
            for command in commands:
                options = A4Options()
                solution = TranslateAlloyToKodkod.execute_command(A4Reporter(), world.getAllSigs(), command, options)
                if command.expects == 1 and not solution.satisfiable():
                    print("Unexpectedly failed to generate instance for positive instance")
                    print(command)
                    commands_as_expected = False
                elif command.expects == 0 and solution.satisfiable():
                    print("Unexpectedly generated instance for negative instance")
                    print(command)
                    commands_as_expected = False
            if not commands_as_expected:
                print(alloy_model_oracle)
                continue

            # check if instances detect erroneous specifications
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


            # save requirement oracle to check next instances
            reqs.append(req['oracle'])