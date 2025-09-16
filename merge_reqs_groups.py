import json
import argparse
import os

def parseArgs():
    parser = argparse.ArgumentParser(description="Script for merging entry groups with challenge requirements")
    parser.add_argument("groups", help="folder with JSONs with entry groups")
    parser.add_argument("reqs", help="JSON with challenge requirements")
    parser.add_argument("-o", "--output", help="Output JSON path (default=merged_reqs.json)", default="merged_reqs.json")
    
    return parser.parse_args()

def main():
    args = parseArgs()
    with open(args.reqs, "r", encoding="utf-8") as file:
        data = json.loads(file.read())

    for model in data:
        print(f"* Processing {model['example']}, id {model['id']}")
        groups = {}
        for filename in os.listdir(args.groups):
            if filename.startswith(model['id']):
                full_path = os.path.join(args.groups, filename)
                with open(full_path, "r", encoding="utf-8") as file:
                    group = json.loads(file.read())
                    groups[group["pred"]] = group
        print(f"Found {len(groups)} challenge groups in {args.groups}")
        for req in model["requirements"]:
            if req["pred"] not in groups:
                print(f"Couldn't find file for {req['pred']}")
            groups_pred_bad = filter(lambda x:x["count"]>1 and not x["correct"],groups[req["pred"]]["groups"])
            groups_pred_good = filter(lambda x:x["correct"],groups[req["pred"]]["groups"])
            req["oracle"] = next(groups_pred_good)["elems"][0]["code"]
            req["erroneous"] = list(map(lambda x:x["elems"][0]["code"],groups_pred_bad))
            print(f"Found {len(req['erroneous'])} erroneous specs for {req['pred']}")

    with open(args.output, 'w') as fp:
        json.dump(data, fp, indent=4)            

if __name__ == "__main__":
    main()