import anthropic
import json
import re
import os
import argparse


def parseArgs():
    parser = argparse.ArgumentParser(description="Script for generating instances using the Claude Opus 4.1 LLM")
    parser.add_argument("prompt", help="the header prompt to be passed to the LLM")
    parser.add_argument("dataset", help="the dataset of natural language requirements")
    parser.add_argument("instances", type=int, help="the number of positive and negative instances to be generated")
    return parser.parse_args()

def main():
    args = parseArgs()

    with open(args.prompt, 'r') as f:
        system_prompt = f.read()

    client = anthropic.Anthropic()

    if not client.api_key:
        print("* LLM API key not configured.")
        return

    instances = int(args.instances)

    #llm = "claude-sonnet-4-5-20250929"
    llm = "claude-opus-4-1-20250805"

    with open(args.dataset, 'r') as f, open(llm+'_'+os.path.basename(args.dataset), 'w') as g:
        dataset = json.load(f)
        for example in dataset:
            print("========================================")
            print(example['example'])
            print("========================================")
            model = example['model']
            reqs = []
            for req in example['requirements']:
                print(req['description'])
                task = f'Generate {instances} positive and {instances} negative instances for the requirement "{req["description"]}" for the following model.' 
                if len(reqs) == 1:
                    task += f' All instances must also satisfy the requirement "{reqs[0]}".'
                elif len(reqs) > 1:
                    task += f' All instances must also satisfy the requirements'
                    for r in reqs[:-1]:
                        task += f'"{r}",'
                    task += f'and "{reqs[-1]}".'
                task += f'\n{model}'
                reqs.append(req['description'])
                while True:
                    try:
                        response = client.with_options(timeout=1000.0).messages.create(
                            model=llm,
                            max_tokens=20000,
                            system=system_prompt,
                            messages=[
                                {"role": "user", "content": task}
                            ],
                            temperature=0
                        )
                    except Exception as e:
                        print(e)
                        continue
                    else:
                        break
                code_blocks = re.findall(r'```alloy(.*?)```', response.content[0].text, re.DOTALL)
                if code_blocks:
                    result = '\n'.join(code_blocks)
                else:
                    result = response.content[0].text

                req['instances'] = result
                req['input tokens'] = response.usage.input_tokens
                req['output tokens'] = response.usage.output_tokens
        json.dump(dataset, g, indent = 4)

if __name__ == "__main__":
    main()