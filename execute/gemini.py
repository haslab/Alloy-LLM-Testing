from google import genai
from google.genai import types
import json
import re
import os
import argparse


def parseArgs():
    parser = argparse.ArgumentParser(description="Script for generating instances using the Gemini-2.5 Pro LLM")
    parser.add_argument("prompt", help="the header prompt to be passed to the LLM")
    parser.add_argument("dataset", help="the dataset of natural language requirements")
    parser.add_argument("instances", type=int, help="the number of positive and negative instances to be generated")
    return parser.parse_args()

def main():
    args = parseArgs()

    with open(args.prompt, 'r') as f:
        system_prompt = f.read()

    try:    
        client = genai.Client()
    except ValueError as e:
        print("* LLM API key not configured.")
        print(e)
        return

    instances = int(args.instances)

    llm = "gemini-2.5-pro"

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
                        response = client.models.generate_content(
                            model=llm,
                            config=types.GenerateContentConfig(system_instruction=system_prompt,temperature=0,seed=0), 
                            contents=task
                        )
                    except Exception as e:
                        print(e)
                        continue
                    else:
                        break

                code_blocks = re.findall(r'```alloy(.*?)```', response.text, re.DOTALL)
                if code_blocks:
                    result = '\n'.join(code_blocks)
                else:
                    result = response.text

                req['instances'] = result
                req['input tokens'] = response.usage_metadata.prompt_token_count
                req['output tokens'] = response.usage_metadata.candidates_token_count + response.usage_metadata.thoughts_token_count
        json.dump(dataset, g, indent = 4)


if __name__ == "__main__":
    main()     

