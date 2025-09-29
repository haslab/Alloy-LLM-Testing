from ollama import generate
import json
import sys
import re

if len(sys.argv) != 4:
    print("Usage: python gpt.py <prompt> <dataset> <instances>")
    sys.exit(1)

with open(sys.argv[1], 'r') as f:
    system_prompt = f.read()

instances = int(sys.argv[3])
llm = "llama3.1:8b"

with open(sys.argv[2], 'r') as f, open(llm+'_'+sys.argv[2], 'w') as g:
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
                    response = generate(model=llm, system=system_prompt, prompt=task)
                except Exception as e:
                    print(e)
                    continue
                else:
                    break

            code_blocks = re.findall(r'```alloy(.*?)```', response.response, re.DOTALL)
            result = '\n'.join(code_blocks)
            req['instances'] = result
            req['input tokens'] = 0
            req['output tokens'] = 0

    json.dump(dataset, g, indent = 4)
