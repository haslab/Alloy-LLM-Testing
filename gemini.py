from google import genai
from google.genai import types
import json
import sys

if len(sys.argv) != 3:
    print("Usage: python gemini.py <prompt> <dataset>")
    sys.exit(1)

with open(sys.argv[1], 'r') as f:
    system_prompt = f.read()

client = genai.Client()

instances = 3
llm = "gemini-2.5-pro"

with open(sys.argv[2], 'r') as f, open(llm+'.json', 'w') as g:
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
            req['instances'] = response.text
            req['tokens'] = response.usage_metadata.total_token_count
    json.dump(dataset, g, indent = 4)


            

