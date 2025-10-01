import anthropic
import json
import sys
import re

if len(sys.argv) != 4:
    print("Usage: python claude.py <prompt> <dataset> <instances>")
    sys.exit(1)

with open(sys.argv[1], 'r') as f:
    system_prompt = f.read()

client = anthropic.Anthropic()

instances = int(sys.argv[3])

llm = "claude-sonnet-4-5-20250929"
#llm = "claude-opus-4-1-20250805"

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


            

