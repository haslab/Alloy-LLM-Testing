import json
import jpype
import jpype.imports
import os.path
import time
import argparse
import gzip
from tqdm import tqdm

from jpype.types import *

def parseArgs():
    parser = argparse.ArgumentParser(description="Script for grouping semantically and syntactically equivalent Alloy predicates")
    parser.add_argument("jar", help="AlloyTools jar path")
    parser.add_argument("entries", help="JSON entry database path")
    parser.add_argument("originals", nargs=argparse.REMAINDER, help="Ids for the models to process")

    parser.add_argument("-o", "--output", help="Output folder path (default=results)", default="results")
    parser.add_argument("-s", "--scope", help="Scope for equivalence tests (default=3)", default=3, type=int)

    return parser.parse_args()

def getEntries(original, db):
    models = {}
    models_challenge = {}
    with gzip.open(db, "rt", encoding="utf-8") as file:
        data = map(json.loads, filter(lambda x: f'"original": "{original}"' in x, file.readlines()))
    
        for entry in data:
            models[entry["_id"]] = entry
            # group entries by cmd
            if "sat" in entry: # execution
                if entry["sat"] != -1: # no error while executing
                    models_challenge.setdefault(entry["cmd_n"],[]).append(entry["_id"])

    return models, models_challenge

def processOriginal(models, original):
    from edu.mit.csail.sdg.parser import CompUtil

    funcs_challenge = {}
    original_world = CompUtil.parseEverything_fromString(None,models[original]["code"])
    original_commands = list(original_world.getAllCommands())
    # identify all commands that call an empty predicate
    for cmd in original_commands:
        for call in cmd.formula.findAllFunctions():
            if call.getBody().toString() == "true": # can't get Java equals() to work?
                funcs_challenge[cmd.label] = call

    return original_commands, funcs_challenge


def main():
    args = parseArgs()

    jpype.startJVM(classpath=[args.jar])

    if not os.path.exists(args.output):
        os.makedirs(args.output)

    with open(Challenge.stats_file(args.output), 'w') as fp:
        fp.write("model\tcmd\tentries\tsemantic\tsyntactic\tscope\tduration\n")

    for original_id in args.originals:

        original_models, models_challenges = getEntries(original_id, args.entries)
        original_commands, funcs_challenge = processOriginal(original_models, original_id)
    
        for challenge_cmd in original_commands:
            challenge_label = str(challenge_cmd.label)
            challenge_models = models_challenges[challenge_label]
            pred_label = str(funcs_challenge[challenge_label].label)
            challenge_obj = Challenge(challenge_label, pred_label, challenge_models, original_models[original_id])
            
            start = time.time()

            if os.path.exists(challenge_obj.output_file(args.output)):
                print(f"{original_id} - {challenge_label} already processed, skipping")
                continue

            for entry in tqdm(challenge_models, desc=f"{original_id} - {challenge_label}", unit="entries"):
                challenge_obj.group(original_models[entry], args.scope)

            if challenge_obj.errors != []:
                print(f"Java failed to parse the following {len(challenge_obj.errors)} entries. This shouldn't happen, DB has been filtered for successful executions.")
                print(challenge_obj.errors)
            if challenge_obj.warns != []:
                print(f"The following {len(challenge_obj.warns)} entries did not have standalone predicates, used helper predicates/functions.")
                print(challenge_obj.warns)

            duration = round(time.time() - start)
            
            challenge_obj.dumpJSON(original_models, duration, args.scope, args.output)

    jpype.shutdownJVM()

class Challenge():

    def __init__(self, cmd, pred, models_challenge, original_id):
        self.cmd = cmd
        self.pred = pred
        self.models = models_challenge
        self.original_id = original_id
        self.groups = []
        self.warns = []
        self.errors = []

    def stats_file(output):
        return f'{output}/grouping_stats.txt'

    def output_file(self, output):
        return f'{output}/{self.original_id["_id"]}_{self.cmd}.json'

    def group(self, entry, scope):
        # test with more popular attempts first
        self.groups.sort(key=lambda x:-len(x))

        code = entry["code"]
        from edu.mit.csail.sdg.parser import CompUtil
        from edu.mit.csail.sdg.translator import A4Options, TranslateAlloyToKodkod
        from edu.mit.csail.sdg.ast import ExprNormalizer
        try:
            world = CompUtil.parseEverything_fromString(None,code)
        except JException as e:
            self.errors.append(entry["_id"])
            return

        for f in world.getAllFunc():
            if f.label == self.pred:
                # if it calls any other local predicate ignore (may call util modules)
                for x in list(f.getBody().findAllFunctions()):
                    if x.label.split("/")[0] == "this":
                        self.warns.append(entry["_id"])
                        return
                        
                normalized = str(ExprNormalizer.normalize(f.getBody()))
                ps = f.getBody().pos()
                ls = code.split("\n")[ps.y-1:ps.y2]
                ls[0] = ls[0][ps.x-1:]
                ls[-1] = ls[-1][:ps.x2]
                challenge_code = "\n".join(ls)
                found = False
                # test if parses as standalone
                test_standalone = f"check {{ {challenge_code} }} for {scope}"
                new_code_standalone = self.original_id["code"] + "\n" + test_standalone
                try:
                    new_world = CompUtil.parseEverything_fromString(None,new_code_standalone)
                except JException as e:
                    self.errors.append(entry["_id"])
                    continue

                for group in self.groups:
                    test = f"check {{ ({challenge_code}) iff ({group[0][1]}) }} for {scope}"
                    new_code = self.original_id["code"] + "\n" + test

                    new_world = CompUtil.parseEverything_fromString(None,new_code)
                    new_cmds = new_world.getAllCommands()
                    solution = TranslateAlloyToKodkod.execute_command(None, new_world.getAllReachableSigs(), new_cmds.get(new_cmds.size()-1), A4Options())
                    if not solution.satisfiable():
                        found = True
                        group.append((entry["_id"],challenge_code,normalized))
                        break

                if not found:
                    self.groups.append([(entry["_id"],challenge_code,normalized)])
                break


    def dumpJSON(self, models, duration, scope, output):
        json_dict = {}
        json_dict["original"] = self.original_id["_id"]
        json_dict["cmd"] = self.cmd
        json_dict["pred"] = self.pred
        json_dict["entry_count"] = len(self.models)
        json_dict["semantic_count"] = len(self.groups)
        json_dict["syntactic_count"] = sum(len({x[2] for x in group}) for group in self.groups)
        json_dict["scope"] = scope
        grps = json_dict.setdefault("groups",[])
        
        for group in self.groups:
            syntactic = []
            uniques = {x[2] for x in group}
            for norm in uniques:
                ids = [x[0:2] for x in group if x[2] == norm]
                syntactic.append({"entry_count":len(ids),"code":ids[0][1],})
            syntactic.sort(key=lambda x:-x["entry_count"])
            grps.append({"entry_count":len(group),"syntactic_count":len(syntactic),"correct":models[group[0][0]]["sat"] != 1,"elems":syntactic})
            
        with open(Challenge.stats_file(output), 'a') as fp:
            fp.write(f'{json_dict["original"]}\t{json_dict["cmd"]}\t{json_dict["entry_count"]}\t{json_dict["semantic_count"]}\t{json_dict["syntactic_count"]}\t{json_dict["scope"]}\t{duration}s\n')

        with open(self.output_file(output), 'w') as fp:
            json.dump(json_dict, fp, indent=4)


if __name__ == "__main__":
    main()