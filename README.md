
This artifact accompanies the FM26 paper entitled "Validating Formal Specifications with LLM-generated Test Cases", which reports an empirical evaluation of using pre-trained large language models (LLMs) to automate the generation of test cases from natural language requirements. 

The artifact provides the scripts, datasets and required tools for reproducing the experiment and the analysis of the results. More specifically, the artifact is split into 3 components:

- **Data preparation**: Scripts to process the existing Alloy4Fun dataset of formal specifications to create the benchmarks for the evaluation. It also contains the pre-computed benchmarks.

- **Experiment execution**: Scripts to execute the experiment for the prepared benchmarks, which involves the use of LLM APIs. Depending on the LLM, this may require an API key. It also contains the pre-computed results from executing the experiment.

- **Result analysis**: Scripts to analyze the results from the experiment, by using a solver to check validity and diversity. It also contains the pre-computed analysis results.

# Data

- [`requirements.json`](./requirements.json): all natural language requirements for which instances were generated, along with pointers to the Alloy4Fun database to retrieve oracles. Each entry consists of the following:
   - `example`: its description
   - `model`: the declaration of its structure in Alloy
   - `id`: the identifier of the model in the Alloy4Fun database containing the oracles
   - `requirements`: the list of requirements for this model, containing a `description` in natural language and the `pred` encoding its oracle
- [`prompt_zero.txt`](./prompt_zero.txt), [`prompt_one.txt`](./prompt_one.txt), and [`prompt_few.txt`](./prompt_few.txt): prompts for the generation of valid/invalid instances from requirements
- [`prompt_few_json.txt`](./prompt_few_json.txt): few-shot prompt for JSON valuations, used by the separate JSON runner
- [`skills/alloy-scenarios`](./skills/alloy-scenarios): a reusable skill based on the few-shot prompt, with [instructions for ChatGPT Work, Chat, and Codex](./skills/alloy-scenarios/README.md). Supply model declarations, a natural language requirement, and separate positive and negative scenario counts. A [ZIP package](./dist/alloy-scenarios.zip) is also available.
- [`models_20250916.json.gz`](./models_20250916.json.gz): a snapshot of the Alloy4Fun database filtered for the exercises used in the evaluation
- [`alloytools.jar`](./alloytools.jar): snapshot of AlloyTools, used to parse and execute Alloy models and commands
- [`prepare`](./prepare): directory containing scripts to retrieve oracles and incorrect submissions from the Alloy4Fun database. It contains:
   - `semantic_grouping.py`: a script to perform grouping of the entries
   - `merge_reqs_groups.py`: a script to merge groups with `requirements.json` for subsequent analysis
   - `results`: a folder with the pre-calculated results for the scripts
- [`execute`](./execute): directory containing scripts to call LLM APIs for the generation of instances given a dataset of requirements and header prompts. It contains:
   - `generate.py`: unified runner, selecting the API from a concrete model ID
   - `generate_json.py`: JSON valuation runner with validation, Alloy rendering, and batched repairs
   - `valuation.py`: model inspection, JSON valuation validation, and conversion to Alloy commands
   - `model_client.py`: shared adapters for OpenAI, Anthropic, Gemini, Ollama, and Codex subscription access
   - `claude.py`, `gemini.py`, `gpt.py`, `llama.py`: compatibility entry points using the original default model IDs
   - `results`: a folder with the pre-calculated results for the scripts
- [`analysis`](./analysis): directory containing analysis scripts to process the LLM-generated instances. It contains:
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

See annotated Alloy [files](analysis/invalid) for the GPT-5, 3 positive / 3 negative instances, few-show prompt, or the raw [failure files](analysis/results).

## RQ5: Effectiveness at detecting incorrect specifications

| Size | Complete | Wrong | Missed | Mean % |
| ---- | -------- | ----- | ------ | ------ |
| [1 pos, 1 neg](analysis/results/gpt-5-2025-08-07_210925_few1.md) | 41 | 5587 | 2204 | 38.10% |
| [2 pos, 2 neg](analysis/results/gpt-5-2025-08-07_220925_few2.md) | 34 | 4623 | 814 | 17.02% |
| [3 pos, 3 neg](analysis/results/gpt-5-2025-08-07_200925_few3.md) | 36 | 4395 | 525 | 9.90% |
| [4 pos, 4 neg](analysis/results/gpt-5-2025-08-07_230925_few4.md) | 35 | 5129 | 446 | 7.45% |
| [5 pos, 5 neg](analysis/results/gpt-5-2025-08-07_230925_few5.md) | 35 | 4816 | 348 | 6.43% |

# Reproducibility

## Setup

The scripts are written in Python and use (through a JPype interface) the Alloy Analyzer (a standalone Java archive). Reproducing the analysis requires: 
 - A JVM (Java 17 or later), with the `JAVA_HOME` correctly set in the environment
 - A Python  installation (3.11 or later) (with the same architecture as the JVM) 

Then install the Python requirements:
```
pip install -r requirements.txt
```

Alternatively, use the provided Dockerfile to create a Docker image and run the scripts from within it:
```
docker build -t alloy-llm-tests . 
docker run -it alloy-llm-tests 
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

This generates a JSON file for each of the selected entries with the grouping information.

Finally, run the merging script into the requirements JSON file:
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

This generates an extended version of the requirements JSON file with grouping information.

### Results

The script was run for models Social Network (`x3JXgWhJ3uti5Dzxz`), Courses (`iP5JL36afv5KbDKP6`), Production line (`dyj49tEp7j6aWAQQX`) and Train Station (`cXPP9QBPTYgTX6WJ6`), with scope 3, for the Alloy4Fun database `models_20250916.json.gz`. Statistics are [here](prepare/results/grouping_stats.txt) and groups in [results folder](prepare/results). Note: this takes a few hours to run.

```
python prepare/semantic_grouping.py alloytools.jar models_20250916.json.gz cXPP9QBPTYgTX6WJ6 x3JXgWhJ3uti5Dzxz iP5JL36afv5KbDKP6 dyj49tEp7j6aWAQQX 
```

These groups have been merged into the provided [requirements](requirements.json) in file [`dataset.json`](prepare/results/dataset.json). Statistics are [here](prepare/results/merging_stats.txt).

```
python prepare/merge_reqs_groups.py prepare/results requirements.json     
```

## Experiment execution

Scripts in folder `execute` call the APIs of the selected LLMs and ask for the generation of instances of the requirements prepared in the previous phase, using one of the provided prompts.

### Usage

Run the unified script with a concrete model ID:

```
python execute/generate.py prompt_few.txt prepare/results/dataset.json 3 --model gpt-5-2025-08-07
```

The positional arguments remain the header prompt, the JSON dataset, and the number of positive **and** negative instances per requirement. The model ID determines the API:

| Model ID | Default platform | Configuration |
| --- | --- | --- |
| `gpt-*`, `chatgpt-*`, `codex*`, `o1`, `o3`, etc. | `gpt-api` (OpenAI Responses API) | `OPENAI_API_KEY` |
| `claude-*` | `claude-api` (Anthropic Messages API) | `ANTHROPIC_API_KEY` |
| `gemini-*` | `gemini-api` (Google GenAI API) | `GEMINI_API_KEY` or `GOOGLE_API_KEY` |
| `deepseek-*` (without a local model tag) | `deepseek-api` (DeepSeek Chat Completions API) | `DEEPSEEK_API_KEY` |
| `llama*` or tagged local IDs such as `qwen3:8b` | `ollama` | A running Ollama server with that model installed; optional `OLLAMA_HOST` |

Provider prefixes (`openai/`, `anthropic/`, `google/`, `models/`, `deepseek/`, and `ollama/`) are also recognized and removed before calling their corresponding APIs. Use `--platform` to override inference, including for an unfamiliar model ID. Only the selected provider's Python SDK is loaded; Codex mode needs no provider SDK.

GPT API calls request disabled prompt caching by sending `prompt_cache_options: {"mode": "explicit"}` without cache breakpoints. This prevents cache reads and writes on GPT-5.6 and later, as described in the [OpenAI prompt-caching guide](https://developers.openai.com/api/docs/guides/prompt-caching). Earlier models, including the original GPT-5 and GPT-5 Mini used in the historical experiment, do not support this control and may reject the request; there is no automatic fallback that enables caching. To run GPT API experiments with caching disabled, select a supported model with `--model`. This request setting applies to `gpt-api` calls; Codex subscription calls use the CLI's behavior.

Claude Messages API calls also run without prompt caching. Claude caching is opt-in: the adapter omits `cache_control` from both the top-level request and all content blocks, as described in the [Claude prompt-caching guide](https://platform.claude.com/docs/en/build-with-claude/prompt-caching). The serialized request is covered by an offline regression check.

DeepSeek calls use the existing OpenAI SDK against `https://api.deepseek.com` with `DEEPSEEK_API_KEY`. Both `generate.py` and `generate_json.py`, including their repair calls, support this provider; `deepseek.py` is a convenience entry point defaulting to `deepseek-flash`. DeepSeek enables [context caching](https://api-docs.deepseek.com/guides/kv_cache/) automatically and documents no cache-off switch. To prevent reuse without changing prompts, each request gets a fresh `user_id`, using DeepSeek's documented [KVCache isolation](https://api-docs.deepseek.com/quick_start/rate_limit/). SDK retries are disabled so the runner's retries also get fresh IDs. This prevents reuse between requests; it does not disable server-side cache creation. Reported hits in either `prompt_cache_hit_tokens` or `prompt_tokens_details.cached_tokens` stop the run. Tagged models such as `deepseek-r1:8b` still use Ollama.

GPT, Claude, Gemini, and DeepSeek API responses are checked for reported cache tokens. If any reported cache-read or cache-write count is positive in these direct API calls, the run stops immediately with an error identifying the provider, model, and reported counts. These responses are not retried or saved to the output file. Codex CLI calls report positive `cached_input_tokens` counts and continue the experiment. Missing or null counters are tolerated; these checks detect reported cache usage rather than proving caching is disabled when usage metadata is unavailable. Gemini requests do not enable explicit caching, but the Developer API can still apply implicit caching; the response check catches any reported cache hits.

For example:

```
python execute/generate.py prompt_few.txt prepare/results/dataset.json 3 --model claude-opus-4-1-20250805
python execute/generate.py prompt_few.txt prepare/results/dataset.json 3 --model gemini-2.5-pro
python execute/generate.py prompt_few.txt prepare/results/dataset.json 3 --model deepseek-flash
python execute/generate_json.py prompt_few_json.txt prepare/results/dataset.json 3 --model deepseek/deepseek-v4-pro
python execute/generate.py prompt_few.txt prepare/results/dataset.json 3 --model llama3.1:8b
python execute/generate.py prompt_few.txt prepare/results/dataset.json 3 --model custom-local-model --platform ollama
```

To use your ChatGPT subscription through Codex, install the Codex CLI, sign in with ChatGPT using `codex login`, then select `--platform codex-cli` and a model available to your subscription:

```
codex login
python execute/generate.py prompt_few.txt prepare/results/dataset.json 3 --model gpt-5 --platform codex-cli -o execute/results/gpt-5_codex_few3.json
```

This uses non-interactive `codex exec` with ChatGPT authentication forced, API-key environment variables removed from the child process, and a fresh temporary working directory in read-only mode. The prompt asks Codex to return only the generated response. The runner searches `PATH` first, then on macOS checks `ChatGPT.app` and `Codex.app` in `/Applications` and `~/Applications`, including the nested CLI bundled with ChatGPT. To choose a specific installation, pass `--codex-exec /path/to/codex` or `--codex-exec /Applications/ChatGPT.app`. See the official [Codex authentication](https://learn.chatgpt.com/docs/auth) and [non-interactive mode](https://learn.chatgpt.com/docs/non-interactive-mode) documentation.

The existing commands, such as `python execute/gpt.py prompt_few.txt prepare/results/dataset.json 3`, still work with their original default model IDs and accept the same new options, including `--model` and `--platform`.

A Dockerfile is also provided to launch the original local `llama3.1:8b` model:
```
docker build -t llama3.1 -f ollama.Dockerfile .
docker run -p 11434:11434 llama3.1
```

Note also that running the script for each LLM may take a few hours.

The output is a JSON file extending the provided `dataset` with `instances`, `input tokens`, and `output tokens` for each requirement, retaining compatibility with the analysis scripts. If no output path is provided, the runner creates `MODEL_PLATFORM_PROMPT_Npos-Nneg_YYYYMMDD-HHMMSS.json` in the current directory, for example `gpt-5_codex-cli_prompt_few_3pos-3neg_20261029-153000.json`. It uses the resolved model ID, the selected or inferred platform, the prompt filename without its extension, the requested positive and negative instance counts per requirement, and the local date and time when the run starts. Characters such as `/`, `:`, and spaces in filename components are replaced by `_`. Pass `-o PATH` or `--output PATH` to choose an explicit output file.

The experiment's prompts, including cumulative constraints from earlier requirements, and Alloy code-block extraction are preserved. Failed model requests are attempted at most three times with a short backoff; use `--attempts N` to change this. Reported cache usage in direct API calls stops the run on the first affected response, regardless of `--attempts`. A failed run exits with an error instead of retrying indefinitely.

Results are saved after each successful requirement, for both explicit and automatically named output paths. Each save atomically replaces the JSON file, so an interruption during writing leaves the previous save intact. If a later call fails or the run is interrupted, completed requirements remain saved; requirements still pending retain their original dataset fields. A response rejected for cache usage is not saved, and earlier results are preserved.

To resume an interrupted run, repeat the command with `--resume` and an explicit `-o PATH` or `--output PATH` pointing to the existing results file:

```
python execute/generate.py prompt_few.txt prepare/results/dataset.json 3 --model gpt-5 --platform codex-cli -o execute/results/gpt-5_codex_few3.json --resume
```

Resume requires a readable JSON file matching the original dataset, including model definitions and requirement order. Requirements with saved `instances`, `input tokens`, and `output tokens` are skipped; missing or incomplete results are generated, preserving cumulative constraints from all earlier requirements. A fully completed file makes no model calls. Recorded prompt hashes, model IDs, platforms, and requested counts are checked before resuming. Older files lacking those settings can still resume; their requested count is recorded from the resume arguments without inventing unavailable original metadata. Without `--resume`, the runner generates every requirement again and replaces any existing output as results arrive.

Every new result records a `generation` object, including when syntax repair is disabled. It contains `mode: "alloy"`, the original response and extracted suite, generation-only token counts, the actual task prompt, the original positive/negative target slots, and `settings`. Settings record the model, platform, system-prompt SHA-256, requested `instances` per classification, absence of an imposed scope, and the Alloy JAR SHA-256 when parser validation is enabled. The shared `generation.settings.instances` field is also used by the JSON-valuation runner and by the analyzer's completeness checks.

To enable an optional Alloy parser feedback loop, pass `--repair-syntax ALLOY_JAR`. This requires Java and JPype, already included in `requirements.txt`:

```
python execute/generate.py prompt_few.txt prepare/results/dataset.json 3 --model llama3.1:8b --repair-syntax alloytools.jar --fix-attempts 3 -o execute/results/llama_repaired.json
```

Each generated run command is compiled independently with the original Alloy model, using the same `CompUtil.parseEverything_fromString` API as `analysis/analyze.py`. This checks syntax, name resolution, and types. Every repair query batches the compiler errors for all currently failing instances of one requirement; passing instances are retained. Repaired instances are checked again, with at most `--fix-attempts N` repair queries per requirement (default: **3**). This limit is separate from `--attempts`, which controls retries when a request fails. Original `expect 0`/`expect 1` classifications are preserved when present. Additional model declarations and facts are rejected. The loop does not run the solver or use requirement oracles, and does not establish semantic correctness or check that the requested number of positive and negative instances was produced.

The original suite and every repair response are retained in the JSON:

- `instances` contains the final suite, and the existing `input tokens`, `output tokens`, and optional `cached input tokens` contain totals across generation and all repair queries, so the analysis scripts continue to read the same fields.
- `generation` contains the original suite, raw model response, and generation-only token counts.
- `syntax repair.rounds` contains each round's feedback, raw response, resulting full suite, and that query's token counts. Malformed repair responses are also recorded and charged, and are not partially applied when their command count differs from the requested batch.
- `syntax repair.errors` records remaining failures; `successful` reports whether every candidate passed, and `complete` reports whether validation finished or the attempt limit was reached. Exhausting the limit prints a warning, retains the last suite and its diagnostics, and continues to the next requirement.

The initial generation and every repair response are saved progressively. Resume with the same `--repair-syntax` option to continue an interrupted repair loop without regenerating saved suites or repeating completed repair queries. Already recorded rounds count against the per-requirement limit. Increasing `--fix-attempts` allows additional rounds for previously exhausted requirements. This can also be used to repair a results file created without repair enabled: add `--resume --repair-syntax alloytools.jar` to the original command with its explicit output path. Existing suites are reused and their original token counts are retained.

Codex token usage is recorded when the CLI reports it, including a `cached input tokens` field per requirement. Positive cached-token counts are reported in the terminal while the run continues and saves its results. Unavailable counts are stored as zero so the existing analysis scripts can still read the results. These counts are usage statistics, not a subscription charge; use zero token costs when analyzing subscription runs. Ollama counts are recorded when reported by the server.

Offline regression checks (no API keys or model calls required):

```
python -m unittest discover -s execute -p 'test_*.py' -v
```

### JSON valuation generation

Use the separate `generate_json.py` entry point with the JSON-oriented prompt. A maximum scope can optionally be supplied:

```
python execute/generate_json.py prompt_few_json.txt prepare/results/dataset.json 3 --model llama3.1:8b --scope 3 -o execute/results/llama_json_few3.json
```

The positional instance count requests that many positive **and** negative valuations. Optional `--scope N` limits each top-level signature to at most N atoms, including zero where the model permits it. If omitted, the runner imposes no population maximum, asks for small instances, and derives the Alloy command's scopes from each returned valuation. Model constraints still apply. The runner supplies the model's signature and field inventory, including domain-qualified field names and tuple arities. It uses the same `ModelClient` adapters and transport options as `generate.py`. Java and JPype are required to inspect the model and compile generated commands; `--alloy-jar PATH` overrides the repository's `alloytools.jar`.

Local Ollama requests use **`--ollama-format schema` by default**. The runner passes a model-derived JSON Schema directly as Ollama's `format` parameter. The schema requires every signature and domain-qualified field key, prohibits extra keys, fixes tuple lengths and scalar column types, and requests exact positive/negative array lengths. When a maximum scope is supplied, top-level atom arrays also receive that upper bound. Repair schemas request only the pending replacement counts, including an empty array for a classification with no pending slots. See [Ollama structured outputs](https://docs.ollama.com/capabilities/structured-outputs).

Use `--ollama-format json` to request Ollama's generic JSON mode without the model-specific schema, or `--ollama-format none` for the previous prompt-only behavior. The setting affects Ollama requests in the JSON runner and is preserved across transport retries. Atom membership, signature hierarchy, ordering, model consistency, and requirement classifications still need the existing validation and analysis; constraining JSON structure alone does not establish logical correctness.

Responses contain `positive` and `negative` arrays. Each valuation contains an `explanation`, a `signatures` object mapping names to atom arrays, and a `fields` object mapping keys such as `Person <: owns` to arrays of tuples. The runner validates required keys, atom membership, scope bounds, tuple arities and types, signature hierarchies, and ordering chains, then generates and compiles the Alloy commands. Only selected atoms are quantified. Actual root populations receive explicit exact scopes, so a smaller ordered population is supported within the requested maximum. It also checks satisfiability of the concrete valuation with the supplied model using SAT4J, rejecting violations of its declarations or facts. Neither target nor earlier requirement oracles are added to this check or sent to the LLM; evaluating the natural language classifications and cumulative requirements remains in `analysis/analyze.py`.

Passing valuations are retained. Missing or invalid slots are batched into one repair query per round, using the same JSON format but requesting only the replacement counts. Each repair request includes the latest rejected valuations, mapped to their original slots, alongside their diagnostics. Missing slots are identified explicitly; if JSON cannot be decoded, the exact raw response is supplied for repair. A shorter repair-specific system prompt keeps attention on editing those valuations. Retained valuations are included as read-only context and cannot be overwritten by a repair response. Identical valuations are detected while ignoring explanations and array order. If an array contains too many entries, the runner considers only its first requested number, in response order; surplus entries remain in the recorded response. Selection does not prefer later entries that happen to pass validation.

Feedback explains simple field multiplicities per atom. For example, a photo without a date receives an error stating that `Photo <: date`, declared with range `one Day`, requires exactly one target for that photo but currently has zero tuples. These errors are also collected from partially malformed valuations, so missing keys do not hide independent declaration errors. Violations of more complex bounds or facts are caught by the Alloy consistency check and reported as an unsatisfiable valuation of the supplied model. Both positive and negative instances must satisfy that model.

`--fix-attempts N` sets the maximum repair queries per requirement, defaulting to **3**; use zero to disable repairs while retaining validation and consistency checks. `--attempts N` separately controls retries of failed model requests. If repairs are exhausted, the runner preserves the accepted portion, records unresolved slots, continues through the remaining requirements, and exits with status 1. Such an output is an incomplete run that can be resumed. A successful run has exactly the requested number of compiled, model-consistent commands in both classifications.

The existing `instances` field contains the final Alloy suite and the existing token fields contain total generation-plus-repair usage, so successful results can be passed directly to `analysis/analyze.py`. `generation` records the original response, decoded valuations when available, its token counts, validation feedback, and rendered initial suite. `json repair.rounds` records the same information for each repair query, including its actual user and system prompts and feedback version; `json repair.accepted` retains each accepted valuation and its command. Requests using native Ollama formatting also record the exact `response format` value (the schema object or `"json"`). Raw responses and costs are saved before validation, and progress is saved after each evaluation. Interrupted validation therefore resumes without repeating the model call or adding its cost again.

Resume using the same command with `--resume` and an explicit output file:

```
python execute/generate_json.py prompt_few_json.txt prepare/results/dataset.json 3 --model llama3.1:8b --scope 3 -o execute/results/llama_json_few3.json --resume
```

JSON mode checks dataset compatibility and saved run settings before issuing requests: resolved model ID, platform, prompt content hash, instance count, maximum scope, Alloy jar content hash, JSON format version, and Ollama format mode must match. It rejects outputs created by the Alloy-text runner. Recorded repair rounds count against the limit; increase `--fix-attempts` when resuming to allow more repairs for exhausted requirements. The Alloy-text `generate.py` workflow remains available separately.

Use a **new output file** to compare schema-constrained generation with older prompt-only runs. Older Ollama results can still be resumed with `--ollama-format none`; resuming them with the new default is rejected to avoid mixing decoding strategies in one experiment. For example, keeping the scope unspecified as in an earlier unbounded run:

```
python execute/generate_json.py prompt_few_json.txt prepare/results/dataset.json 3 --model llama3.1:8b --ollama-format schema -o fac-exps/llama_json_schema_few3.json
```

When resuming results from the earlier JSON validator, saved responses are revalidated locally using the new consistency checks. Old acceptance decisions, diagnostics, and rendered suites are archived under `validation history`; raw responses, token totals, and the number of used repair queries are preserved. A previously accepted valuation that violates a model declaration is therefore returned to the repair queue. This revalidation does not issue model requests; additional repair requests still require room within `--fix-attempts`.

### Results

The script was run for a few combinations of LLMs (GPT-5, GPT5 Mini, Gemini 2.5 Pro, Claude Opus 4.1), the provided prompts (`prompt_zero.txt`, `prompt_one.txt` and `prompt_few.txt`), and number of instances (from 1 to 5), for the requirements in [`dataset.json`](prepare/results/dataset.json).

For instance, for GPT-5, few-shot prompt and 3 instances, the following command should be run:

```
python execute/generate.py prompt_few.txt prepare/results/dataset.json 3 --model gpt-5-2025-08-07
```

The pre-computed results of the generation process as extended JSON files are collected in [execute/results](execute/results).

## Results analysis

Scripts in folder `analysis` process the instances generated by the LLMs and use AlloyTools to check its syntactic and semantic validity, as well as how many erroneous entries in the Alloy4Fun dataset would be detected.

### Usage

For each of the JSON files containing LLM-generated instances, the generation script is run as:

```
usage: analyze.py process [-h] [--max-coverage RESULTS_JSON] jar results icost ocost

positional arguments:
  jar         AlloyTools jar path
  results     JSON LLM instance generation results
  icost       input cost
  ocost       output cost

options:
  -h, --help  show this help message and exit
  --max-coverage RESULTS_JSON
              optional minimal/run_rates.py results.json for comparison with the optimum
```

The LLM token cost can be passed to print total cost statistics.

This script reports overall results in terms of valid and failing instances, both in textual `.txt` and markdown `.md` format. Additionally, it provides a JSON file reporting all failing instances for inspection.

Each generated `run` command is counted, including malformed commands and commands missing an explicit `expect 0` or `expect 1` clause; these fail the syntax check. Expectations written only in comments do not classify a test. Empty suites are incomplete, and percentages with zero denominators are reported as zero.

The `Defined` column immediately after `Consistent` checks semantic uniqueness modulo atom renaming within each command's original signature scopes and integer bitwidth. After finding a satisfying instance of the test predicate P, the analyzer encodes all its visible signatures, fields, and ordering successors in a complete instance predicate I with existentially bound, distinct atoms. It then asks whether P and not I has a solution. Unsatisfiability establishes that every satisfying instance is isomorphic to the first; satisfiability detects genuine underspecification. Named singleton atoms, signature aliases, assignments by row, and distinctness implied by exact scopes are accepted when they determine a unique structure. A recognized complete quantified-atom encoding certifies uniqueness directly and avoids the second solver call. Skolem witnesses and private module implementation relations are ignored; integer and string values retain their identities. The check uses declarations and model facts, without adding the target oracle or earlier requirement oracles, and currently supports static signatures and fields. Failures are recorded under `defined` and excluded from later validity, completeness, and coverage checks. Difficult semantic queries can take substantially longer than the syntactic fast path.

For complete valid suites, `Wrong` counts the parseable erroneous specifications, `Detected` counts those detected by the suite, and `% of total` reports `100 × Detected / Wrong`. Example subtotals and the overall total sum the specification counts and report the unweighted mean of per-requirement detection percentages over complete suites.

The `n` column, immediately after `Requirement`, reads the requested count per classification from `generation.settings.instances`, or from the initial `generation.targets` when settings are absent. Older files without count metadata fall back to filenames such as `_3pos-3neg_...` or `_few3`; the report and console mention this only when that fallback is used. Generated test counts never substitute for requested counts. `Complete` requires exactly n positive and n negative tests, all valid. If n cannot be determined, it is shown as `—` and the suite is not marked complete.

The `Repair calls` column, after `Cost`, counts additional corrective LLM requests recorded in `syntax repair.rounds` or `json repair.rounds`. Batched and unsuccessful repair requests each count once; the initial response and API/network retries are excluded. `0` indicates enabled repair handling without corrective requests, and `—` indicates disabled or unavailable repair tracking. Example subtotals and the overall total sum recorded calls only when every included requirement has a known count; otherwise they show `—`. Token and cost columns already include recorded repair usage.

Optionally pass the JSON results saved by `minimal/run_rates.py` to compare detection with the best possible suite of the same size and scope. For the scope-4 results, run from `fac-exps` (replace `RUN.json`, `ICOST`, and `OCOST`):

```sh
python ../analysis/analyze.py process ../alloytools.jar RUN.json ICOST OCOST --max-coverage ../minimal/results/results.json
```

This adds three comparison columns:

- `Complete ≤4`: exactly n positive and n negative tests, all passing the existing validity checks, with every possible instance of each test using at most four atoms per top-level signature under the declarations and earlier requirements. Actual populations are checked with Alloy; a larger declared command bound alone does not exclude a fixed small instance. Abstract parents count as top-level signatures, and their descendants share that population.
- `Max detected`: the exact optimum for the benchmark, invariant, n, and reference scope. Sizes skipped after an earlier 100% result inherit that certified optimum.
- `% of max`: `100 × Detected / Max detected`, reported only for complete suites within the reference scope and matching specification totals. Equivalent specification rewrites are accepted. If the reference directory contains its saved `dataset.json`, declarations, oracles, and earlier requirements are also checked.

Subtotals count complete suites within the reference scope, sum their maximum detection counts, and report the unweighted mean of their individual `% of max` values. Ineligible suites show `—` for the comparison. Missing optima, differing specification totals, or detection exceeding the saved optimum produce a warning and an unavailable comparison; a missing eligible comparison also makes the corresponding aggregate unavailable. A zero optimum has no defined percentage. The scope is read from the results file and appears in the column heading. The same optional argument is supported by `all`. Without it, the report format and analysis remain unchanged.

Alternatively, the analysis can be run for a set of LLM executions specified in a JSON file.

```
usage: analyze.py all [-h] [--max-coverage RESULTS_JSON] jar execs

positional arguments:
  jar         AlloyTools jar path
  execs       JSON file reporting a set of LLM executions and costs

options:
  -h, --help  show this help message and exit
```

### Comparing generated tests across runs

Use `analysis/compare_runs.py` to compare two or more generation-results JSON files modulo atom renaming:

```sh
python analysis/compare_runs.py alloytools.jar RUN1.json RUN2.json RUN3.json -o fac-exps/overlap
```

This saves `fac-exps/overlap.md` and `fac-exps/overlap.json`, leaving the input files unchanged. Inputs must contain the same benchmarks, requirements, model declarations, oracles, and cumulative requirement order; requested suite sizes and generated test counts may differ. Use the AlloyTools jar, not the AlloyMax jar.

The script constructs one catalogue of structural classes across all runs, separately for each benchmark, requirement, and intended positive/negative label. It verifies satisfiability and uniqueness modulo symmetry using the same checks as `analyze.py`. To match another test P against a class representative, it asks whether P and the representative's complete instance predicate I is satisfiable, preserving P's original scopes and bitwidth. Signatures, fields, and ordering successors are compared; integer and string values keep their identities. Tests with syntax errors, inconsistent tests, and tests admitting multiple structures are excluded, with counts and reasons reported.

For each run, the reports give the number of compared tests, distinct structures, duplicate occurrences, and distinct structures found **only in that run**. They also provide pairwise intersections and Jaccard percentages, the union and intersection across all runs, the number of classes appearing in exactly k runs, and a breakdown by requirement and polarity. Duplicate occurrences count once in overlap sets. Jaccard is intersection divided by union; an empty union has no defined percentage. The JSON includes all commands, their class assignments, and a complete representative predicate for every class.

By default, all consistent tests with a unique structure are compared, including tests that violate earlier requirements or have incorrect expected labels. Add `--valid-only` to restrict structural overlap to tests that also satisfy earlier requirement oracles and have the correct polarity for the target oracle.

Both modes check validity afresh for a separate **invalid-test recurrence** report covering every generated command. For each requirement it gives the invalid-test count in each run, recurrence in 0/k through k/k runs, and counts by first failing stage: syntax, consistency, uniqueness, earlier requirements, or target oracle. The report also includes a recurrence frequency distribution and pairwise/all-run overlap of the sets of requirements with invalid tests. Invalid duplicate commands count as separate occurrences, while recurrence counts runs. All requirements, including those with no observed failures, appear in the JSON and Markdown reports. Per-command JSON records include `validity` and, for failures, `failure_stage` and `reason`; failure summaries are under `failure_recurrence`.

Solver errors and unsupported encodings are reported as unassessed rather than invalid, with assessment gaps highlighted in the recurrence report. Missing tests concern completeness and do not count as invalid commands. Recurrence at the same requirement or stage does not by itself prove the same misunderstanding caused the failures. Neither mode relies on saved analysis reports. Uniqueness and comparison currently support static signatures and fields; semantic checks can take longer for encodings without explicit complete valuations. Because validity is now checked in both modes, a default comparison can take longer than with the earlier version of this script.

### Results

To run the analysis for an LLM execution the following command should be run, in this case for GPT-5, few-shot prompt and 3 instances:

```
python analysis/analyze.py process alloytools.jar execute/results/gpt-5-2025-08-07_230925_few3.json 1.25 10
```

Running the analysis for all executions of the benchmark can be done with the following command. Note that this takes about 30 minutes to execute.

```
python analysis/analyze.py all alloytools.jar execute/results/results.json
```

The script was run for all LLM executions, whose JSON files are stored in [execute/results](execute/results). These pre-computed results of the analysis process are in [analysis/results](analysis/results), containing the overall results in textual `.txt` and markdown `.md` format. The JSON files reporting failing instances are contained in [analysis/invalid](analysis/invalid).
