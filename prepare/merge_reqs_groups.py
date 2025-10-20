import json
import argparse
import os

def parseArgs():
    parser = argparse.ArgumentParser(description="Script for merging entry groups with challenge requirements")
    parser.add_argument("groups", help="folder with JSONs with entry groups")
    parser.add_argument("reqs", help="JSON with challenge requirements")
    parser.add_argument("-o", "--output", help="Output JSON path (default=dataset.json)", default="dataset.json")
    parser.add_argument("-t", "--threshold", help="Member group filtering threshold (default=2)", default=2, type=int)
    
    return parser.parse_args()

def main():
    args = parseArgs()
    with open(args.reqs, "r", encoding="utf-8") as file:
        data = json.loads(file.read())

    with open("merging_stats.txt", 'w') as fp:
        fp.write(f"id\tpred\ttotal\twrong\tfilter\n")

    for model in data:

        groups = {}
        for filename in os.listdir(args.groups):
            if filename.startswith(model['id']):
                full_path = os.path.join(args.groups, filename)
                with open(full_path, "r", encoding="utf-8") as file:
                    group = json.loads(file.read())
                    groups[group["pred"]] = group

        for req in model["requirements"]:
            if req["pred"] not in groups:
                print(f"Couldn't find file for {model['id']} - {req['pred']}, skipping")
                continue
            groups_pred_bad = list(filter(lambda x:not x["correct"],groups[req["pred"]]["groups"]))
            groups_pred_filter = list(filter(lambda x:x["entry_count"]>=args.threshold,groups_pred_bad))
            groups_pred_good = filter(lambda x:x["correct"],groups[req["pred"]]["groups"])
            req["oracle"] = next(groups_pred_good)["elems"][0]["code"]
            req["erroneous"] = list(map(lambda x:x["elems"][0]["code"],groups_pred_filter))
            with open("merging_stats.txt", 'a') as fp:
                fp.write(f'{model["id"]}\t{req["pred"]}\t{groups[req["pred"]]["semantic_count"]}\t{len(groups_pred_bad)}\t{len(groups_pred_filter)}\n')

    with open(args.output, 'w') as fp:
        json.dump(data, fp, indent=4)            

if __name__ == "__main__":
    main()