# Structural overlap between generated test runs

Tests are grouped separately for each benchmark, requirement, and intended polarity. Only satisfiable tests with an explicit expect 0/1 and a unique visible structure modulo atom renaming are compared. Each structure is encoded as a complete instance predicate I; another test P matches when P and I is satisfiable under P's original scopes and integer bitwidth. Signatures, fields, and ordering successors are preserved; integer/string values retain their identities. Skolem witnesses and private module implementation relations are ignored. Different commands encoding the same structure count once in overlap sets. No larger comparison scope is introduced.

Cohort: **consistent and unique**. Structural overlap includes consistent, unique tests even when they fail earlier requirements or have incorrect labels.
Validity is always checked afresh for the separate invalid-test recurrence section.

- **run1**: `/Users/alcino/Projectos/Alloy-LLM-Testing/fac-exps/claude-sonnet-5-5_claude-api_prompt_few_gpt_3pos-3neg_20261103-172111.json`
- **run2**: `/Users/alcino/Projectos/Alloy-LLM-Testing/fac-exps/claude-sonnet-5-5_claude-api_prompt_few_gpt_3pos-3neg_20261103-174824.json`
- **run3**: `/Users/alcino/Projectos/Alloy-LLM-Testing/fac-exps/claude-sonnet-5-5_claude-api_prompt_few_gpt_3pos-3neg_20261103-180936.json`

## Per-run diversity

`Distinct` counts different structures within that run. `Duplicates` counts repeated occurrences beyond the first. `Only this run` counts distinct classes absent from every other supplied run. These counts keep requirements and intended polarities separate.

| Run | Generated | Compared | Distinct | Duplicates | Only this run | Excluded |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| run1 | 258 | 257 | 257 | 0 | 182 | 1 |
| run2 | 258 | 257 | 257 | 0 | 174 | 1 |
| run3 | 258 | 256 | 256 | 0 | 168 | 2 |

Exclusions (first failing stage; commands and reasons are retained in the JSON report):

| Run | inconsistent | syntax |
| --- | ---: | ---: |
| run1 | 0 | 1 |
| run2 | 1 | 0 |
| run3 | 1 | 1 |

## Overlap across all runs

Union: **629** distinct classes. Present in every run: **36**. All-run Jaccard (intersection / union): **5.72%**. All structural sets identical: **no**.

| Number of runs containing a class | Classes |
| ---: | ---: |
| 1 | 524 |
| 2 | 69 |
| 3 | 36 |

## Pairwise overlap

Jaccard = shared classes / union of classes. Empty unions have no defined percentage. Counts use sets, so repeated tests do not increase overlap.

| Runs | Shared | Union | Jaccard | Left only | Right only | Same set |
| --- | ---: | ---: | ---: | ---: | ---: | :---: |
| run1 / run2 | 53 | 461 | 11.50% | 204 | 204 | no |
| run1 / run3 | 58 | 455 | 12.75% | 199 | 198 | no |
| run2 / run3 | 66 | 447 | 14.77% | 191 | 190 | no |

## Invalid-test recurrence

Validity is checked for every generated command independently of the structural comparison cohort. Commands are assigned their first failing stage: syntax, consistency, uniqueness, preceding requirement oracles, or target oracle. Counts include repeated command occurrences. Recurrence measures which requirements have at least one invalid test in each run; it does not establish that the same semantic misunderstanding occurred. Solver errors and unsupported encodings are unassessed, not confirmed invalid. Missing tests concern suite completeness and do not count as invalid commands.

This section covers all generated commands, including those excluded by `--valid-only`.

| Run | Generated | Valid | Invalid | Unassessed | Requirements with invalid tests |
| --- | ---: | ---: | ---: | ---: | ---: |
| run1 | 258 | 254 | 4 | 0 | 2 |
| run2 | 258 | 253 | 5 | 0 | 2 |
| run3 | 258 | 253 | 5 | 0 | 3 |

Requirements with invalid tests in at least one run: **5**. Requirements with invalid tests in every run: **1**. All-run Jaccard of affected-requirement sets: **20.00%**.

| Observed invalid tests in this many runs | Requirements | Of these, fully assessed |
| ---: | ---: | ---: |
| 0/3 | 38 | 38 |
| 1/3 | 4 | 4 |
| 2/3 | 0 | 0 |
| 3/3 | 1 | 1 |

### Invalid-test counts per requirement

| Benchmark | Requirement | Runs with invalid tests | run1 | run2 | run3 | Unassessed commands |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| Photo sharing social network | inv1 | 0/3 | 0 | 0 | 0 | 0 |
| Photo sharing social network | inv2 | 0/3 | 0 | 0 | 0 | 0 |
| Photo sharing social network | inv3 | 1/3 | 0 | 1 | 0 | 0 |
| Photo sharing social network | inv4 | 0/3 | 0 | 0 | 0 | 0 |
| Photo sharing social network | inv5 | 0/3 | 0 | 0 | 0 | 0 |
| Photo sharing social network | inv6 | 0/3 | 0 | 0 | 0 | 0 |
| Photo sharing social network | inv7 | 0/3 | 0 | 0 | 0 | 0 |
| Photo sharing social network | inv8 | 0/3 | 0 | 0 | 0 | 0 |
| Production line | inv1 | 0/3 | 0 | 0 | 0 | 0 |
| Production line | inv2 | 0/3 | 0 | 0 | 0 | 0 |
| Production line | inv3 | 0/3 | 0 | 0 | 0 | 0 |
| Production line | inv4 | 0/3 | 0 | 0 | 0 | 0 |
| Production line | inv5 | 0/3 | 0 | 0 | 0 | 0 |
| Production line | inv6 | 0/3 | 0 | 0 | 0 | 0 |
| Production line | inv7 | 0/3 | 0 | 0 | 0 | 0 |
| Production line | inv8 | 0/3 | 0 | 0 | 0 | 0 |
| Production line | inv9 | 0/3 | 0 | 0 | 0 | 0 |
| Production line | inv10 | 0/3 | 0 | 0 | 0 | 0 |
| Train station | inv1 | 0/3 | 0 | 0 | 0 | 0 |
| Train station | inv2 | 0/3 | 0 | 0 | 0 | 0 |
| Train station | inv3 | 0/3 | 0 | 0 | 0 | 0 |
| Train station | inv4 | 0/3 | 0 | 0 | 0 | 0 |
| Train station | inv5 | 1/3 | 0 | 0 | 1 | 0 |
| Train station | inv6 | 1/3 | 0 | 0 | 1 | 0 |
| Train station | inv7 | 0/3 | 0 | 0 | 0 | 0 |
| Train station | inv8 | 0/3 | 0 | 0 | 0 | 0 |
| Train station | inv9 | 0/3 | 0 | 0 | 0 | 0 |
| Train station | inv10 | 0/3 | 0 | 0 | 0 | 0 |
| Courses | inv1 | 0/3 | 0 | 0 | 0 | 0 |
| Courses | inv2 | 0/3 | 0 | 0 | 0 | 0 |
| Courses | inv3 | 0/3 | 0 | 0 | 0 | 0 |
| Courses | inv4 | 0/3 | 0 | 0 | 0 | 0 |
| Courses | inv5 | 0/3 | 0 | 0 | 0 | 0 |
| Courses | inv6 | 0/3 | 0 | 0 | 0 | 0 |
| Courses | inv7 | 0/3 | 0 | 0 | 0 | 0 |
| Courses | inv8 | 0/3 | 0 | 0 | 0 | 0 |
| Courses | inv9 | 3/3 | 3 | 4 | 3 | 0 |
| Courses | inv10 | 0/3 | 0 | 0 | 0 | 0 |
| Courses | inv11 | 0/3 | 0 | 0 | 0 | 0 |
| Courses | inv12 | 0/3 | 0 | 0 | 0 | 0 |
| Courses | inv13 | 1/3 | 1 | 0 | 0 | 0 |
| Courses | inv14 | 0/3 | 0 | 0 | 0 | 0 |
| Courses | inv15 | 0/3 | 0 | 0 | 0 | 0 |

### Recurrence by first failing stage

Only stages with observed failures are listed. Counts are invalid command occurrences, including repetitions within a run.

| Benchmark | Requirement | First failing stage | Runs with this failure | run1 | run2 | run3 |
| --- | --- | --- | ---: | ---: | ---: | ---: |
| Photo sharing social network | inv3 | oracle | 1/3 | 0 | 1 | 0 |
| Train station | inv5 | inconsistent | 1/3 | 0 | 0 | 1 |
| Train station | inv6 | syntax | 1/3 | 0 | 0 | 1 |
| Courses | inv9 | syntax | 1/3 | 1 | 0 | 0 |
| Courses | inv9 | inconsistent | 1/3 | 0 | 1 | 0 |
| Courses | inv9 | oracle | 3/3 | 2 | 3 | 3 |
| Courses | inv13 | oracle | 1/3 | 1 | 0 | 0 |

### Pairwise overlap of affected requirements

| Runs | Affected in both | Affected in either | Jaccard | Same affected requirements |
| --- | ---: | ---: | ---: | :---: |
| run1 / run2 | 1 | 3 | 33.33% | no |
| run1 / run3 | 1 | 4 | 25.00% | no |
| run2 / run3 | 1 | 4 | 25.00% | no |

## Distinct structures per requirement and polarity

| Benchmark | Requirement | Polarity | Union | In every run | run1 | run2 | run3 |
| --- | --- | --- | ---: | ---: | ---: | ---: | ---: |
| Photo sharing social network | inv1 | positive | 8 | 0 | 3 | 3 | 3 |
| Photo sharing social network | inv1 | negative | 8 | 0 | 3 | 3 | 3 |
| Photo sharing social network | inv2 | positive | 7 | 1 | 3 | 3 | 3 |
| Photo sharing social network | inv2 | negative | 7 | 1 | 3 | 3 | 3 |
| Photo sharing social network | inv3 | positive | 8 | 0 | 3 | 3 | 3 |
| Photo sharing social network | inv3 | negative | 7 | 1 | 3 | 3 | 3 |
| Photo sharing social network | inv4 | positive | 8 | 0 | 3 | 3 | 3 |
| Photo sharing social network | inv4 | negative | 7 | 1 | 3 | 3 | 3 |
| Photo sharing social network | inv5 | positive | 8 | 0 | 3 | 3 | 3 |
| Photo sharing social network | inv5 | negative | 7 | 1 | 3 | 3 | 3 |
| Photo sharing social network | inv6 | positive | 8 | 0 | 3 | 3 | 3 |
| Photo sharing social network | inv6 | negative | 8 | 0 | 3 | 3 | 3 |
| Photo sharing social network | inv7 | positive | 8 | 0 | 3 | 3 | 3 |
| Photo sharing social network | inv7 | negative | 5 | 2 | 3 | 3 | 3 |
| Photo sharing social network | inv8 | positive | 7 | 1 | 3 | 3 | 3 |
| Photo sharing social network | inv8 | negative | 8 | 0 | 3 | 3 | 3 |
| Production line | inv1 | positive | 8 | 0 | 3 | 3 | 3 |
| Production line | inv1 | negative | 7 | 1 | 3 | 3 | 3 |
| Production line | inv2 | positive | 8 | 0 | 3 | 3 | 3 |
| Production line | inv2 | negative | 7 | 0 | 3 | 3 | 3 |
| Production line | inv3 | positive | 8 | 0 | 3 | 3 | 3 |
| Production line | inv3 | negative | 9 | 0 | 3 | 3 | 3 |
| Production line | inv4 | positive | 7 | 1 | 3 | 3 | 3 |
| Production line | inv4 | negative | 8 | 0 | 3 | 3 | 3 |
| Production line | inv5 | positive | 7 | 0 | 3 | 3 | 3 |
| Production line | inv5 | negative | 6 | 1 | 3 | 3 | 3 |
| Production line | inv6 | positive | 7 | 1 | 3 | 3 | 3 |
| Production line | inv6 | negative | 8 | 0 | 3 | 3 | 3 |
| Production line | inv7 | positive | 7 | 1 | 3 | 3 | 3 |
| Production line | inv7 | negative | 8 | 0 | 3 | 3 | 3 |
| Production line | inv8 | positive | 8 | 0 | 3 | 3 | 3 |
| Production line | inv8 | negative | 7 | 1 | 3 | 3 | 3 |
| Production line | inv9 | positive | 7 | 1 | 3 | 3 | 3 |
| Production line | inv9 | negative | 8 | 0 | 3 | 3 | 3 |
| Production line | inv10 | positive | 8 | 0 | 3 | 3 | 3 |
| Production line | inv10 | negative | 7 | 1 | 3 | 3 | 3 |
| Train station | inv1 | positive | 7 | 0 | 3 | 3 | 3 |
| Train station | inv1 | negative | 8 | 0 | 3 | 3 | 3 |
| Train station | inv2 | positive | 7 | 0 | 3 | 3 | 3 |
| Train station | inv2 | negative | 9 | 0 | 3 | 3 | 3 |
| Train station | inv3 | positive | 8 | 0 | 3 | 3 | 3 |
| Train station | inv3 | negative | 7 | 0 | 3 | 3 | 3 |
| Train station | inv4 | positive | 5 | 2 | 3 | 3 | 3 |
| Train station | inv4 | negative | 9 | 0 | 3 | 3 | 3 |
| Train station | inv5 | positive | 8 | 0 | 3 | 3 | 2 |
| Train station | inv5 | negative | 7 | 1 | 3 | 3 | 3 |
| Train station | inv6 | positive | 6 | 1 | 3 | 3 | 3 |
| Train station | inv6 | negative | 5 | 0 | 3 | 3 | 2 |
| Train station | inv7 | positive | 4 | 2 | 3 | 3 | 3 |
| Train station | inv7 | negative | 8 | 0 | 3 | 3 | 3 |
| Train station | inv8 | positive | 4 | 2 | 3 | 3 | 3 |
| Train station | inv8 | negative | 7 | 1 | 3 | 3 | 3 |
| Train station | inv9 | positive | 7 | 0 | 3 | 3 | 3 |
| Train station | inv9 | negative | 7 | 0 | 3 | 3 | 3 |
| Train station | inv10 | positive | 5 | 1 | 3 | 3 | 3 |
| Train station | inv10 | negative | 7 | 0 | 3 | 3 | 3 |
| Courses | inv1 | positive | 9 | 0 | 3 | 3 | 3 |
| Courses | inv1 | negative | 9 | 0 | 3 | 3 | 3 |
| Courses | inv2 | positive | 9 | 0 | 3 | 3 | 3 |
| Courses | inv2 | negative | 8 | 0 | 3 | 3 | 3 |
| Courses | inv3 | positive | 8 | 0 | 3 | 3 | 3 |
| Courses | inv3 | negative | 8 | 0 | 3 | 3 | 3 |
| Courses | inv4 | positive | 8 | 0 | 3 | 3 | 3 |
| Courses | inv4 | negative | 8 | 0 | 3 | 3 | 3 |
| Courses | inv5 | positive | 7 | 0 | 3 | 3 | 3 |
| Courses | inv5 | negative | 8 | 0 | 3 | 3 | 3 |
| Courses | inv6 | positive | 6 | 1 | 3 | 3 | 3 |
| Courses | inv6 | negative | 8 | 0 | 3 | 3 | 3 |
| Courses | inv7 | positive | 8 | 0 | 3 | 3 | 3 |
| Courses | inv7 | negative | 8 | 0 | 3 | 3 | 3 |
| Courses | inv8 | positive | 6 | 1 | 3 | 3 | 3 |
| Courses | inv8 | negative | 8 | 0 | 3 | 3 | 3 |
| Courses | inv9 | positive | 8 | 0 | 3 | 2 | 3 |
| Courses | inv9 | negative | 6 | 1 | 2 | 3 | 3 |
| Courses | inv10 | positive | 7 | 0 | 3 | 3 | 3 |
| Courses | inv10 | negative | 9 | 0 | 3 | 3 | 3 |
| Courses | inv11 | positive | 9 | 0 | 3 | 3 | 3 |
| Courses | inv11 | negative | 5 | 2 | 3 | 3 | 3 |
| Courses | inv12 | positive | 7 | 0 | 3 | 3 | 3 |
| Courses | inv12 | negative | 8 | 0 | 3 | 3 | 3 |
| Courses | inv13 | positive | 5 | 1 | 3 | 3 | 3 |
| Courses | inv13 | negative | 7 | 1 | 3 | 3 | 3 |
| Courses | inv14 | positive | 8 | 0 | 3 | 3 | 3 |
| Courses | inv14 | negative | 7 | 1 | 3 | 3 | 3 |
| Courses | inv15 | positive | 8 | 0 | 3 | 3 | 3 |
| Courses | inv15 | negative | 5 | 2 | 3 | 3 | 3 |

Class IDs, complete representative predicates, every command's class assignment, per-requirement pairwise statistics, and exclusions are available in the JSON report.
