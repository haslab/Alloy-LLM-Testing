from openai import OpenAI
import json
import sys

if len(sys.argv) != 3:
    print("Usage: python gpt.py <prompt> <dataset>")
    sys.exit(1)

with open(sys.argv[1], 'r') as f:
    system_prompt = f.read()

client = OpenAI()

instances = 3
llm = "gpt-5-2025-08-07"

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
            if response.output_text.startswith("```alloy"):
                instances = response.output_text[8:-3]
            else:
                instances = response.output_text
            req['instances'] = instances
            req['input tokens'] = response.usage.input_tokens
            req['output tokens'] = response.usage.output_tokens
    json.dump(dataset, g, indent = 4)


            

