# Data

- [`requirements.json`](./requirements.json): all requirements for which instances were generated, along with pointers to the Alloy4Fun database to retrieve oracles. Each entry consists of the following:
   - `example`: its description
   - `model`: the declaration of its structure in Alloy
   - `id`: the identifier of the model in the Alloy4Fun database containing the oracles
   - `requirements`: the list of requirements for this model, containing a `description` in natural language and the `pred` encoding its oracle
- [`prompt_zero.txt`](./prompt_zero.txt), [`prompt_one.txt`](./prompt_one.txt), and [`prompt_few.txt`](./prompt_few.txt): prompts for the generation of valid/invalid instances from requirements
- [`models_20250916.json.gz`](./models_20250916.json.gz): a snapshot of the Alloy4Fun database for the selected exercises
- [`alloytools.jar`](./alloytools.jar): snapshot of AlloyTools, used to parse and execute Alloy models and commands
- [`prepare`](./prepare): directory containing scripts to retrieve oracles and incorrect submissions from Alloy4Fun database. It contains:
   - `semantic_grouping.py`: a script to perform grouping of the entries
   - `merge_reqs_groups.py`: a script to merge groups with `requirements.json` for subsequent analysis
   - `results`: a folder with the pre-calculated results for the scripts
- [`execute`](./execute): directory containing scripts to call LLM APIs for the generation of instances given a dataset of requirements and header prompts
   - `claude.py`: script for Claude Opus 4.1
   - `gemini.py`: script for Gemini 2.5 Pro
   - `gpt.py`: script for GPT-5 and GPT-5 Mini
   - `llama.py`: script for Llama 3.1
   - `results`: a folder with the pre-calculated results for the scripts
- [`analysis`](./analysis): directory containing analysis scripts to process the LLM-generated instances
   - `analysis.py`: script for testing syntactic and semantic correctness of generated instances, as well as diversity
   - `results`: a folder with the pre-calculated results for the scripts
   - `invalid`: a folder containing invalid generated instances with annotations

# Results

## RQ1: Influence of prompt design

| Prompt | Tests | Syntax | Scopes | Previous | Valid | % | Cost |
| ------ | ----- | ------ | ------ | -------- | ----- | - | ---- |
| [Few-shot](analysis/results/gpt-5-2025-08-07_200925_few3.md) | 258 | 255 | 255 | 252 | 247 | 96% | $3.56 |
| [One-shot](analysis/results/gpt-5-2025-08-07_200925_one3.md) | 258 | 226 | 208 | 206 | 205 | 79% | $3.69 |
| [Zero-shot](analysis/results/gpt-5-2025-08-07_210925_zero3.md) | 258 | 137 | 120 | 119 | 118 | 46% | $4.20 |

## RQ2: Effect of non-determinism

| Run | Tests | Syntax | Scopes | Previous | Valid | % | Cost |
| ------ | ----- | ------ | ------ | -------- | ----- | - | ---- |
| [1st](analysis/results/gpt-5-2025-08-07_200925_few3.md) | 258 | 255 | 255 | 252 | 247 | 96% | $3.56 |
| [2nd](analysis/results/gpt-5-2025-08-07_220925_few3.md) | 258 | 256 | 256 | 256 | 251 | 97% | $3.50 |
| [3rd](analysis/results/gpt-5-2025-08-07_230925_few3.md) | 258 | 252 | 252 | 250 | 246 | 95% | $3.61 |

## RQ3: LLM comparison

| Model | Tests | Syntax | Scopes | Previous | Valid | % | Cost |
| ------ | ----- | ------ | ------ | -------- | ----- | - | ---- |
| [GPT-5](analysis/results/gpt-5-2025-08-07_200925_few3.md) | 258 | 255 | 255 | 252 | 247 | 96% | $3.56 |
| [Gemini 2.5 Pro](analysis/results/gemini-2.5-pro_210925_few3.md) | 258 | 248 | 220 | 212 | 210 | 81% | $2.78 |
| [Claude Opus 4.1](analysis/results/claude-opus-4-1-20250805_210925_few3.md) | 258 | 258 | 258 | 202 | 197 | 76% | $5.55 |
| [GPT-5 Mini](analysis/results/gpt-5-mini-2025-08-07_290925_few3.md) | 258 | 188 | 183 | 179 | 174 | 67% | $0.53 |

## RQ4: Characterization of invalid test cases

See annotated Alloy [files](analysis/invalid) for the GPT-5, 3 pos, 3 neg, few-show prompt, or the raw [failure files](analysis/results).

## RQ5: Effectiveness at detecting incorrect specifications

| Size | Complete | Wrong | Missed | Mean % |
| ---- | -------- | ----- | ------ | ------ |
| [1 pos, 1 neg](analysis/results/gpt-5-2025-08-07_210925_few1.md) | 41 | 5579 | 2202 | 38.10% |
| [2 pos, 2 neg](analysis/results/gpt-5-2025-08-07_220925_few2.md) | 34 | 4617 | 814 | 17.02% |
| [3 pos, 3 neg](analysis/results/gpt-5-2025-08-07_200925_few3.md) | 36 | 4387 | 524 | 9.91% |
| [4 pos, 4 neg](analysis/results/gpt-5-2025-08-07_230925_few4.md) | 35 | 5121 | 444 | 7.44% |
| [5 pos, 5 neg](analysis/results/gpt-5-2025-08-07_230925_few5.md) | 35 | 4809 | 348 | 6.43% |

# Scripts

Start by installing the requirements.

```
pip install -r requirements.txt
```

## Data preparation

Script `semantic_grouping.py` groups together all entries of an Alloy4Fun database that have been submitted to given challenges. Entries are grouped when semantically equivalent according to the Alloy solver (i.e., equivalence within a certain scope). Since the solver is called to compare entries, this may take some time.

Two entries are equivalent for a challenge if the predicate to be filled by the student are equivalent (identified as an empty predicate called from a check command in the root model). This has a few consequences:
- This ignores any pre-condition in the check. This means that there may be multiple correct groups (which were equivalent under the pre-conditions).
- If the student used any auxiliary predicate, the test will fail, since these are not copied into the test (there are few cases, identified in the log).

The script only considers execution entries that are syntactically correct in the database (no sharing entries, nor errored). 

Script `merge_reqs_groups.py` can then be used to insert erroneous specifications into the provided `requirements.json`. The mapping is done via the predicate name: for each example in `requirements.json` (identified by id in the Alloy4Fun database), each requirement must have the student predicate defined. The script will search for the corresponding groups among the files generated by `semantic_grouping.py`. The script ignores groups with only 1 entry (i.e., submissions that have only been attempted once).

### Usage

Run the grouping script as:

```
usage: semantic_grouping.py [-h] [-o OUTPUT] [-s SCOPE] jar entries ...

Script for grouping semantically and syntactically equivalent Alloy predicates

positional arguments:
  jar                   AlloyTools jar path
  entries               JSON entry database path
  originals             Ids for the models to process

optional arguments:
  -h, --help            show this help message and exit
  -o OUTPUT, --output OUTPUT
                        Output folder path (default=results)
  -s SCOPE, --scope SCOPE
                        Scope for equivalence tests (default=3)
```

Finally, run the merging script into the requirements:
```
usage: merge_reqs_groups.py [-h] [-o OUTPUT] [-t THRESHOLD] groups reqs

Script for merging entry groups with challenge requirements

positional arguments:
  groups                folder with JSONs with entry groups
  reqs                  JSON with challenge requirements

optional arguments:
  -h, --help            show this help message and exit
  -o OUTPUT, --output OUTPUT
                        Output JSON path (default=dataset.json)
  -t THRESHOLD, --threshold THRESHOLD
                        Member group filtering threshold (default=2)
```

### Results

The script was run for models Social Network (`x3JXgWhJ3uti5Dzxz`), Courses (`iP5JL36afv5KbDKP6`), Production line (`dyj49tEp7j6aWAQQX`) and Train Station (`cXPP9QBPTYgTX6WJ6`), with scope 3, for the Alloy4Fun database `models_20250916.json.gz`. Statistics are [here](prepare/results/grouping_stats.txt) and groups in [results folder](prepare/results). Note: this takes a few hours to run.

```
python3 semantic_grouping.py ./alloytools.jar ./models_20250916.json.gz cXPP9QBPTYgTX6WJ6 x3JXgWhJ3uti5Dzxz iP5JL36afv5KbDKP6 dyj49tEp7j6aWAQQX
```

This groups have merged into the provided [requirements](requirements.json) in file [`dataset.json`](prepare/results/dataset.json). Statistics are [here](prepare/results/merging_stats.txt).

```
python3 merge_reqs_groups.py results requirements.json
```

## Experiment execution

Scripts in folder `execute` call the APIs of the selected LLMs and ask for the generation of instances of the requirements prepared in the previous phase, using one of the provided prompts.

### Usage

For each of the supported LLMs, the generation script is run as:

```
Usage: python3 <LLM>.py <prompt> <dataset> <instances>
```

Where `<prompt>` is a header prompt to be passed to the LLM, `<dataset>` is the result of the preparation phase, and `<intances>` is the number of positive and negative instances to be generated.

### Results

The script was run for some combinations of LLMs (GPT-5, GPT5 Mini, Gemini 2.5 Pro, Claude Opus 4.1), the provided prompts (`prompt_zero.txt`, `prompt_one.txt` and `prompt_few.txt`), and number of instances (from 1 to 5), for the requirements in [`dataset.json`](prepare/results/dataset.json).

For instance, for GPT-5, few-shot prompt and 3 instances, the following command should be run:

```
python3 gpt.py prompt_few.txt dataset.json 3
```

The results of the generation process are collected in [execute/results](execute/results), where each requirement in the JSON is extended by a field `instances` constaining the generated instances. 
