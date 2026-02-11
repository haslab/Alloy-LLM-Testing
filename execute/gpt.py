from openai import OpenAI,OpenAIError
import json
import re
import os
import argparse


def parseArgs():
    parser = argparse.ArgumentParser(description="Script for generating instances using the GPT-5 LLM")
    parser.add_argument("prompt", help="the header prompt to be passed to the LLM")
    parser.add_argument("dataset", help="the dataset of natural language requirements")
    parser.add_argument("instances", type=int, help="the number of positive and negative instances to be generated")
    return parser.parse_args()

def main():
    args = parseArgs()

    with open(args.prompt, 'r') as f:
        system_prompt = f.read()

    try:    
        client = OpenAI()
    except OpenAIError as e:
        print("* LLM API key not configured.")
        print(e)
        return

    instances = int(args.instances)

    #llm = "gpt-5-mini-2025-08-07"
    llm = "gpt-5-2025-08-07"

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
                        response = client.responses.create(
                            model=llm,
                            instructions=system_prompt,
                            input=task,
                            # Temperature not supported in gpt-5
                            # temperature=0
                        )
                    except Exception as e:
                        print(e)
                        continue
                    else:
                        break

                code_blocks = re.findall(r'```alloy(.*?)```', response.output_text, re.DOTALL)
                if code_blocks:
                    result = '\n'.join(code_blocks)
                else:
                    result = response.output_text

                req['instances'] = result
                req['input tokens'] = response.usage.input_tokens
                req['output tokens'] = response.usage.output_tokens
        json.dump(dataset, g, indent = 4)


if __name__ == "__main__":
    main()            

