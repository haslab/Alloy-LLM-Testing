import json
import jpype
import jpype.imports
import gzip
from jpype.types import *
import os.path
import time
import argparse
from tqdm import tqdm

models, models_challenge = {}, {}

def main():
    args = parseArgs()

    jpype.startJVM(classpath=[args.jar])

    for original_model in args.originals:
        if not os.path.exists(args.output):
            os.makedirs(args.output)

        getEntries(original_model, args.entries)
        original_commands, funcs_challenge = processOriginal(original_model)
    
        print(f"* Processing challenge {original_model}, {len(models)} entries, {len(funcs_challenge)} commands")

        for challenge in sorted(models_challenge):
            try:
                cmd = original_commands[challenge]
            except:
                print("Does not exist in original:", challenge)
                continue
            print(f"** Processing command #{challenge}, {cmd}, testing {funcs_challenge[cmd.label]}, {len(models_challenge[challenge])} entries")
            start = time.time()

            output_file_path = f'{args.output}/{original_model}_{challenge}.json'
            if os.path.exists(output_file_path):
                print(f"Command #{challenge}, {cmd} already processed, skipping")
                continue

            challenge_groups = []
            warns = []
            errors = []

            for entry in tqdm(models_challenge[challenge], desc="Processing", unit="entries"):    
                challenge_groups.sort(key=lambda x:-len(x))
                checkEquiv(entry, original_model, funcs_challenge[cmd.label].label, errors, warns, challenge_groups, args.scope)

            if errors != []:
                print(f"Java failed to parse the following {len(errors)} entries. This shouldn't happen, DB has been filtered for successful executions.")
                print(errors)
            if warns != []:
                print(f"Java failed to check equivalences for the following {len(warns)} pairs. Usually because code uses helper predicates/functions besides the challenge invariant.")
                print(warns)

            duration = round(time.time() - start)
            
            print(f"Found {len(challenge_groups)} semantic groups in {duration}s, with sizes:")
            print(list(map(len,challenge_groups)))
            print()

            cmd = original_commands[challenge]
            dumpJSON(str(cmd.label), str(funcs_challenge[cmd.label].label), duration, args.scope, len(models_challenge[challenge]), challenge_groups, output_file_path)

    jpype.shutdownJVM()

def dumpJSON(cmd,pred,duration,scope,entries,groups,output):
    json_dict = {}
    json_dict["label"] = cmd
    json_dict["pred"] = pred
    json_dict["entry_count"] = entries
    json_dict["group_count"] = len(groups)
    json_dict["duration"] = duration
    json_dict["scope"] = scope
    grps = json_dict.setdefault("groups",[])
    
    for group in groups:
        lst = list(map(lambda x: {"id":x[0], "code":x[1]}, group))
        grps.append({"count":len(lst),"elems":lst,"correct":models[group[0][0]]["sat"] != 1})
        
    with open(output, 'w') as fp:
        json.dump(json_dict, fp, indent=4)

def getEntries(original, fjson):
    models.clear()
    models_challenge.clear()
    with gzip.open(fjson, "rt", encoding="utf-8") as file:
        ls = filter(lambda x: f'"original":"{original}"' in x, file.readlines())
        data = map(json.loads,ls)
    
        for entry in data:
            models[entry["_id"]] = entry
            if "sat" in entry: # execution
                if entry["sat"] != -1: # no error while executing
                    models_challenge.setdefault(entry["cmd_i"],[]).append(entry["_id"])
    
def processOriginal(original):
    from edu.mit.csail.sdg.parser import CompUtil

    funcs_challenge = {}
    original_world = CompUtil.parseEverything_fromString(None,models[original]["code"])
    original_commands = list(original_world.getAllCommands())
    for cmd in original_commands:
        for call in cmd.formula.findAllFunctions():
            if call.getBody().toString() == "true": # can't get Java equals() to work?
                funcs_challenge[cmd.label] = call

    return original_commands, funcs_challenge

def parseArgs():
    parser = argparse.ArgumentParser(description="Script for grouping semantically equivalent Alloy entries")
    parser.add_argument("jar", help="AlloyTools jar path")
    parser.add_argument("entries", help="JSON entry database path")
    parser.add_argument("originals", nargs=argparse.REMAINDER, help="Ids for the models to process")

    parser.add_argument("-o", "--output", help="Output folder path (default=results)", default="results")
    parser.add_argument("-s", "--scope", help="Scope for equivalence tests (default=3)", default=3)

    return parser.parse_args()

def checkEquiv(entry, original, pred, errors, warns, groups, scope):
    code = models[entry]["code"]
    from edu.mit.csail.sdg.parser import CompUtil
    from edu.mit.csail.sdg.translator import A4Options, TranslateAlloyToKodkod
    try:
        world = CompUtil.parseEverything_fromString(None,code)
    except JException as e:
        errors.append(entry)
        # print(e)                
        return

    for f in world.getAllFunc():
        if f.label == pred:
            ps = f.getBody().pos()
            ls = code.split("\n")[ps.y-1:ps.y2]
            ls[0] = ls[0][ps.x-1:]
            ls[-1] = ls[-1][:ps.x2]
            challenge_code = "\n".join(ls)
            found = False
            failed = False
            for group in groups:
                test = f"check {{ ({challenge_code}) iff ({group[0][1]}) }} for {scope}"
                new_code = models[original]["code"] + "\n" + test

                try:
                    new_world = CompUtil.parseEverything_fromString(None,new_code)
                    new_cmds = new_world.getAllCommands()
                    solution = TranslateAlloyToKodkod.execute_command(None, new_world.getAllReachableSigs(), new_cmds.get(new_cmds.size()-1), A4Options())
                    if not solution.satisfiable():
                        found = True
                        group.append((entry,challenge_code))
                        break
                except JException as e:
                    warns.append((entry,group[0][0]))
                    # print(e)                            

            if not found:
                groups.append([(entry,challenge_code)])
            break


if __name__ == "__main__":
    main()