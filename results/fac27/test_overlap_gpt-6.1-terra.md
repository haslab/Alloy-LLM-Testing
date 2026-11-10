# Structural and fault-detection overlap between generated test runs

Tests are grouped separately for each benchmark, requirement, and intended polarity. Only satisfiable tests with an explicit expect 0/1 and a unique visible structure modulo atom renaming are compared. Each structure is encoded as a complete instance predicate I; another test P matches when P and I is satisfiable under P's original scopes and integer bitwidth. Signatures, fields, and ordering successors are preserved; integer/string values retain their identities. Skolem witnesses and private module implementation relations are ignored. Different commands encoding the same structure count once in overlap sets. No larger comparison scope is introduced.

Cohort: **consistent and unique**. Structural overlap includes consistent, unique tests even when they fail earlier requirements or have incorrect labels.
Validity is always checked afresh for the separate invalid-test recurrence section.

- **run1**: `/Users/alcino/Projectos/Alloy-LLM-Testing/results/fac27/gpt-6.1-terra_gpt-api_prompt_few_gpt_3pos-3neg_20261102-172937.json`
- **run2**: `/Users/alcino/Projectos/Alloy-LLM-Testing/results/fac27/gpt-6.1-terra_gpt-api_prompt_few_gpt_3pos-3neg_20261103-103849.json`
- **run3**: `/Users/alcino/Projectos/Alloy-LLM-Testing/results/fac27/gpt-6.1-terra_gpt-api_prompt_few_gpt_3pos-3neg_20261103-114029.json`

## Per-run diversity

`Distinct` counts different structures within that run. `Duplicates` counts repeated occurrences beyond the first. `Only this run` counts distinct classes absent from every other supplied run. These counts keep requirements and intended polarities separate.

| Run | Generated | Compared | Distinct | Duplicates | Only this run | Excluded |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| run1 | 258 | 258 | 258 | 0 | 110 | 0 |
| run2 | 258 | 258 | 258 | 0 | 104 | 0 |
| run3 | 258 | 257 | 257 | 0 | 111 | 1 |

Exclusions (first failing stage; commands and reasons are retained in the JSON report):

| Run | syntax |
| --- | ---: |
| run1 | 0 |
| run2 | 0 |
| run3 | 1 |

## Overlap across all runs

Union: **500** distinct classes. Present in every run: **98**. All-run Jaccard (intersection / union): **19.60%**. All structural sets identical: **no**.

| Number of runs containing a class | Classes |
| ---: | ---: |
| 1 | 325 |
| 2 | 77 |
| 3 | 98 |

## Pairwise overlap

Jaccard = shared classes / union of classes. Empty unions have no defined percentage. Counts use sets, so repeated tests do not increase overlap.

| Runs | Shared | Union | Jaccard | Left only | Right only | Same set |
| --- | ---: | ---: | ---: | ---: | ---: | :---: |
| run1 / run2 | 127 | 389 | 32.65% | 131 | 131 | no |
| run1 / run3 | 119 | 396 | 30.05% | 139 | 138 | no |
| run2 / run3 | 125 | 390 | 32.05% | 133 | 132 | no |

## Invalid-test recurrence

Validity is checked for every generated command independently of the structural comparison cohort. Commands are assigned their first failing stage: syntax, consistency, uniqueness, preceding requirement oracles, or target oracle. Counts include repeated command occurrences. Recurrence measures which requirements have at least one invalid test in each run; it does not establish that the same semantic misunderstanding occurred. Solver errors and unsupported encodings are unassessed, not confirmed invalid. Missing tests concern suite completeness and do not count as invalid commands.

This section covers all generated commands, including those excluded by `--valid-only`.

| Run | Generated | Valid | Invalid | Unassessed | Requirements with invalid tests |
| --- | ---: | ---: | ---: | ---: | ---: |
| run1 | 258 | 253 | 5 | 0 | 3 |
| run2 | 258 | 253 | 5 | 0 | 3 |
| run3 | 258 | 251 | 7 | 0 | 5 |

Requirements with invalid tests in at least one run: **5**. Requirements with invalid tests in every run: **3**. All-run Jaccard of affected-requirement sets: **60.00%**.

| Observed invalid tests in this many runs | Requirements | Of these, fully assessed |
| ---: | ---: | ---: |
| 0/3 | 38 | 38 |
| 1/3 | 2 | 2 |
| 2/3 | 0 | 0 |
| 3/3 | 3 | 3 |

### Invalid-test counts per requirement

| Benchmark | Requirement | Runs with invalid tests | run1 | run2 | run3 | Unassessed commands |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| Photo sharing social network | inv1 | 0/3 | 0 | 0 | 0 | 0 |
| Photo sharing social network | inv2 | 0/3 | 0 | 0 | 0 | 0 |
| Photo sharing social network | inv3 | 3/3 | 1 | 1 | 1 | 0 |
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
| Production line | inv6 | 3/3 | 1 | 1 | 1 | 0 |
| Production line | inv7 | 0/3 | 0 | 0 | 0 | 0 |
| Production line | inv8 | 0/3 | 0 | 0 | 0 | 0 |
| Production line | inv9 | 0/3 | 0 | 0 | 0 | 0 |
| Production line | inv10 | 1/3 | 0 | 0 | 1 | 0 |
| Train station | inv1 | 0/3 | 0 | 0 | 0 | 0 |
| Train station | inv2 | 0/3 | 0 | 0 | 0 | 0 |
| Train station | inv3 | 0/3 | 0 | 0 | 0 | 0 |
| Train station | inv4 | 0/3 | 0 | 0 | 0 | 0 |
| Train station | inv5 | 0/3 | 0 | 0 | 0 | 0 |
| Train station | inv6 | 0/3 | 0 | 0 | 0 | 0 |
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
| Courses | inv7 | 1/3 | 0 | 0 | 1 | 0 |
| Courses | inv8 | 0/3 | 0 | 0 | 0 | 0 |
| Courses | inv9 | 3/3 | 3 | 3 | 3 | 0 |
| Courses | inv10 | 0/3 | 0 | 0 | 0 | 0 |
| Courses | inv11 | 0/3 | 0 | 0 | 0 | 0 |
| Courses | inv12 | 0/3 | 0 | 0 | 0 | 0 |
| Courses | inv13 | 0/3 | 0 | 0 | 0 | 0 |
| Courses | inv14 | 0/3 | 0 | 0 | 0 | 0 |
| Courses | inv15 | 0/3 | 0 | 0 | 0 | 0 |

### Recurrence by first failing stage

Only stages with observed failures are listed. Counts are invalid command occurrences, including repetitions within a run.

| Benchmark | Requirement | First failing stage | Runs with this failure | run1 | run2 | run3 |
| --- | --- | --- | ---: | ---: | ---: | ---: |
| Photo sharing social network | inv3 | oracle | 3/3 | 1 | 1 | 1 |
| Production line | inv6 | oracle | 3/3 | 1 | 1 | 1 |
| Production line | inv10 | previous | 1/3 | 0 | 0 | 1 |
| Courses | inv7 | syntax | 1/3 | 0 | 0 | 1 |
| Courses | inv9 | oracle | 3/3 | 3 | 3 | 3 |

### Pairwise overlap of affected requirements

| Runs | Affected in both | Affected in either | Jaccard | Same affected requirements |
| --- | ---: | ---: | ---: | :---: |
| run1 / run2 | 3 | 3 | 100.00% | yes |
| run1 / run3 | 3 | 5 | 60.00% | no |
| run2 / run3 | 3 | 5 | 60.00% | no |

## Overlap in detected and missed specifications

Fault detection is compared only for requirements with a complete valid suite in every run. Requested counts come from generation metadata or recognized filenames, never generated counts. All runs use the same erroneous-specification catalogue and preceding requirement oracles. A specification is detected if at least one test disagrees with its expect annotation when that specification replaces the target oracle. Tests retain their original scopes and bitwidth. Exact duplicate specifications are counted once; IDs hash the benchmark, requirement, and specification text with leading/trailing whitespace removed. Unparseable specifications and specifications with an unassessed outcome in any run are excluded from every run's denominator and reported separately, never counted as missed. Empty set unions have no defined Jaccard. Primary averages weight requirements equally; pooled statistics are also provided. Agreement establishes discrimination against this fault catalogue, not scenario equivalence.

Requirements with complete valid suites and a shared catalogue: **38/43**. Requirements with at least one assessed specification: **38**. Assessed specifications: **4297**. Unparseable specifications excluded: **0**. Specifications with assessment gaps: **0**.

### Detection and benefit of combining runs

Coverage below is the unweighted mean of per-requirement detection rates on the shared assessed catalogue. Counts are pooled; they do not determine the mean coverage. `Only this run` counts specifications detected by that run and missed by every other run.

| Run | Detected | Missed | Only this run | Mean coverage |
| --- | ---: | ---: | ---: | ---: |
| run1 | 3883 | 414 | 16 | 91.48% |
| run2 | 3901 | 396 | 24 | 90.55% |
| run3 | 3928 | 369 | 104 | 92.07% |

Combined mean coverage: **95.46%**; best individual run: **92.07%**; gain: **3.38 percentage points**.

Pooled combined detection: **4069/4297**; best individual run: **3928**; additional specifications detected: **141**.

The combined result uses every test from every run and therefore a larger test budget. Mean coverage gain compares the combined suite with the best single run across the shared requirements, rather than selecting a different best run for each requirement.

### Pairwise overlap of detected and missed sets

Primary Jaccard values are averaged per requirement. The number of contributing requirements can differ between detected and missed sets because empty unions are undefined.

| Runs | Mean detected Jaccard | Requirements | Mean missed Jaccard | Requirements |
| --- | ---: | ---: | ---: | ---: |
| run1 / run2 | 95.19% | 38 | 58.66% | 37 |
| run1 / run3 | 93.81% | 38 | 52.09% | 37 |
| run2 / run3 | 92.95% | 38 | 48.87% | 37 |

Pooled overlap is also shown; requirements with more faulty specifications have more weight here.

| Runs | Detected shared | Detected union | Detected Jaccard | Left only | Right only | Missed shared | Missed union | Missed Jaccard |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| run1 / run2 | 3819 | 3965 | 96.32% | 64 | 82 | 332 | 478 | 69.46% |
| run1 / run3 | 3766 | 4045 | 93.10% | 117 | 162 | 252 | 531 | 47.46% |
| run2 / run3 | 3776 | 4053 | 93.17% | 125 | 152 | 244 | 521 | 46.83% |

**Detected in all runs:** 3718; **detected in any run:** 4069; mean all-run Jaccard: **91.09%** (38 requirements); pooled all-run Jaccard: **91.37%**.

**Missed in all runs:** 228; **missed in any run:** 579; mean all-run Jaccard: **37.68%** (37 requirements); pooled all-run Jaccard: **39.38%**.

### Fault detection per requirement

Per-requirement gain uses that requirement's best individual suite as its baseline.

| Benchmark | Requirement | Assessed faults | Best run | Combined | Gain | Gain (pp) | Detected Jaccard | Missed Jaccard |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Photo sharing social network | inv1 | 126 | 125 | 126 | 1 | 0.79 | 96.83% | 0.00% |
| Photo sharing social network | inv2 | 44 | 43 | 43 | 0 | 0.00 | 95.35% | 33.33% |
| Photo sharing social network | inv4 | 127 | 121 | 122 | 1 | 0.79 | 91.80% | 33.33% |
| Photo sharing social network | inv5 | 121 | 121 | 121 | 0 | 0.00 | 95.87% | 0.00% |
| Photo sharing social network | inv6 | 71 | 66 | 67 | 1 | 1.41 | 97.01% | 66.67% |
| Photo sharing social network | inv7 | 464 | 459 | 460 | 1 | 0.22 | 93.70% | 12.12% |
| Photo sharing social network | inv8 | 179 | 164 | 167 | 3 | 1.68 | 68.86% | 18.75% |
| Production line | inv1 | 50 | 48 | 48 | 0 | 0.00 | 89.58% | 28.57% |
| Production line | inv2 | 92 | 89 | 91 | 2 | 2.17 | 94.51% | 16.67% |
| Production line | inv3 | 31 | 31 | 31 | 0 | 0.00 | 100.00% | — |
| Production line | inv4 | 85 | 82 | 82 | 0 | 0.00 | 96.34% | 50.00% |
| Production line | inv5 | 66 | 63 | 63 | 0 | 0.00 | 96.83% | 60.00% |
| Production line | inv7 | 78 | 74 | 76 | 2 | 2.56 | 88.16% | 18.18% |
| Production line | inv8 | 78 | 74 | 75 | 1 | 1.28 | 93.33% | 37.50% |
| Production line | inv9 | 647 | 570 | 581 | 11 | 1.70 | 88.64% | 50.00% |
| Train station | inv1 | 134 | 133 | 133 | 0 | 0.00 | 98.50% | 33.33% |
| Train station | inv2 | 48 | 47 | 48 | 1 | 2.08 | 89.58% | 0.00% |
| Train station | inv3 | 122 | 116 | 116 | 0 | 0.00 | 94.83% | 50.00% |
| Train station | inv4 | 77 | 74 | 77 | 3 | 3.90 | 88.31% | 0.00% |
| Train station | inv5 | 136 | 132 | 132 | 0 | 0.00 | 96.97% | 50.00% |
| Train station | inv6 | 52 | 48 | 48 | 0 | 0.00 | 100.00% | 100.00% |
| Train station | inv7 | 20 | 18 | 18 | 0 | 0.00 | 94.44% | 66.67% |
| Train station | inv8 | 20 | 19 | 20 | 1 | 5.00 | 60.00% | 0.00% |
| Train station | inv9 | 143 | 139 | 139 | 0 | 0.00 | 97.12% | 50.00% |
| Train station | inv10 | 48 | 43 | 47 | 4 | 8.33 | 85.11% | 12.50% |
| Courses | inv1 | 166 | 155 | 161 | 6 | 3.61 | 85.09% | 17.24% |
| Courses | inv2 | 34 | 30 | 31 | 1 | 2.94 | 87.10% | 42.86% |
| Courses | inv3 | 65 | 62 | 62 | 0 | 0.00 | 100.00% | 100.00% |
| Courses | inv4 | 86 | 84 | 85 | 1 | 1.16 | 92.94% | 14.29% |
| Courses | inv5 | 205 | 177 | 179 | 2 | 0.98 | 94.41% | 72.22% |
| Courses | inv6 | 111 | 93 | 94 | 1 | 0.90 | 89.36% | 62.96% |
| Courses | inv8 | 62 | 56 | 57 | 1 | 1.61 | 87.72% | 41.67% |
| Courses | inv10 | 69 | 66 | 67 | 1 | 1.45 | 95.52% | 40.00% |
| Courses | inv11 | 66 | 59 | 63 | 4 | 6.06 | 79.37% | 18.75% |
| Courses | inv12 | 54 | 53 | 53 | 0 | 0.00 | 86.79% | 12.50% |
| Courses | inv13 | 206 | 184 | 184 | 0 | 0.00 | 96.20% | 75.86% |
| Courses | inv14 | 41 | 39 | 39 | 0 | 0.00 | 97.44% | 66.67% |
| Courses | inv15 | 73 | 59 | 63 | 4 | 5.48 | 77.78% | 41.67% |

### Requirements excluded from fault-detection comparison

Structural comparison and invalid-test recurrence still include these requirements.

| Benchmark | Requirement | Reason |
| --- | --- | --- |
| Photo sharing social network | inv3 | run1: suite is not complete and valid; run2: suite is not complete and valid; run3: suite is not complete and valid |
| Production line | inv6 | run1: suite is not complete and valid; run2: suite is not complete and valid; run3: suite is not complete and valid |
| Production line | inv10 | run3: suite is not complete and valid |
| Courses | inv7 | run3: suite is not complete and valid |
| Courses | inv9 | run1: suite is not complete and valid; run2: suite is not complete and valid; run3: suite is not complete and valid |

The JSON report includes stable specification IDs and source text, per-run detected/missed IDs, individual outcomes, per-requirement overlap and gains, and catalogue exclusions.

## Distinct structures per requirement and polarity

| Benchmark | Requirement | Polarity | Union | In every run | run1 | run2 | run3 |
| --- | --- | --- | ---: | ---: | ---: | ---: | ---: |
| Photo sharing social network | inv1 | positive | 6 | 1 | 3 | 3 | 3 |
| Photo sharing social network | inv1 | negative | 4 | 2 | 3 | 3 | 3 |
| Photo sharing social network | inv2 | positive | 7 | 1 | 3 | 3 | 3 |
| Photo sharing social network | inv2 | negative | 7 | 1 | 3 | 3 | 3 |
| Photo sharing social network | inv3 | positive | 7 | 1 | 3 | 3 | 3 |
| Photo sharing social network | inv3 | negative | 7 | 0 | 3 | 3 | 3 |
| Photo sharing social network | inv4 | positive | 5 | 1 | 3 | 3 | 3 |
| Photo sharing social network | inv4 | negative | 6 | 1 | 3 | 3 | 3 |
| Photo sharing social network | inv5 | positive | 7 | 0 | 3 | 3 | 3 |
| Photo sharing social network | inv5 | negative | 7 | 1 | 3 | 3 | 3 |
| Photo sharing social network | inv6 | positive | 7 | 0 | 3 | 3 | 3 |
| Photo sharing social network | inv6 | negative | 5 | 1 | 3 | 3 | 3 |
| Photo sharing social network | inv7 | positive | 7 | 0 | 3 | 3 | 3 |
| Photo sharing social network | inv7 | negative | 5 | 1 | 3 | 3 | 3 |
| Photo sharing social network | inv8 | positive | 8 | 0 | 3 | 3 | 3 |
| Photo sharing social network | inv8 | negative | 8 | 0 | 3 | 3 | 3 |
| Production line | inv1 | positive | 6 | 1 | 3 | 3 | 3 |
| Production line | inv1 | negative | 7 | 1 | 3 | 3 | 3 |
| Production line | inv2 | positive | 5 | 1 | 3 | 3 | 3 |
| Production line | inv2 | negative | 5 | 1 | 3 | 3 | 3 |
| Production line | inv3 | positive | 8 | 0 | 3 | 3 | 3 |
| Production line | inv3 | negative | 6 | 1 | 3 | 3 | 3 |
| Production line | inv4 | positive | 6 | 1 | 3 | 3 | 3 |
| Production line | inv4 | negative | 7 | 1 | 3 | 3 | 3 |
| Production line | inv5 | positive | 7 | 1 | 3 | 3 | 3 |
| Production line | inv5 | negative | 7 | 1 | 3 | 3 | 3 |
| Production line | inv6 | positive | 5 | 1 | 3 | 3 | 3 |
| Production line | inv6 | negative | 5 | 2 | 3 | 3 | 3 |
| Production line | inv7 | positive | 6 | 0 | 3 | 3 | 3 |
| Production line | inv7 | negative | 7 | 1 | 3 | 3 | 3 |
| Production line | inv8 | positive | 5 | 2 | 3 | 3 | 3 |
| Production line | inv8 | negative | 5 | 1 | 3 | 3 | 3 |
| Production line | inv9 | positive | 7 | 1 | 3 | 3 | 3 |
| Production line | inv9 | negative | 7 | 1 | 3 | 3 | 3 |
| Production line | inv10 | positive | 9 | 0 | 3 | 3 | 3 |
| Production line | inv10 | negative | 8 | 0 | 3 | 3 | 3 |
| Train station | inv1 | positive | 6 | 1 | 3 | 3 | 3 |
| Train station | inv1 | negative | 4 | 2 | 3 | 3 | 3 |
| Train station | inv2 | positive | 6 | 1 | 3 | 3 | 3 |
| Train station | inv2 | negative | 5 | 2 | 3 | 3 | 3 |
| Train station | inv3 | positive | 5 | 2 | 3 | 3 | 3 |
| Train station | inv3 | negative | 5 | 2 | 3 | 3 | 3 |
| Train station | inv4 | positive | 6 | 1 | 3 | 3 | 3 |
| Train station | inv4 | negative | 7 | 0 | 3 | 3 | 3 |
| Train station | inv5 | positive | 7 | 1 | 3 | 3 | 3 |
| Train station | inv5 | negative | 5 | 2 | 3 | 3 | 3 |
| Train station | inv6 | positive | 6 | 1 | 3 | 3 | 3 |
| Train station | inv6 | negative | 4 | 2 | 3 | 3 | 3 |
| Train station | inv7 | positive | 4 | 2 | 3 | 3 | 3 |
| Train station | inv7 | negative | 4 | 2 | 3 | 3 | 3 |
| Train station | inv8 | positive | 5 | 1 | 3 | 3 | 3 |
| Train station | inv8 | negative | 5 | 2 | 3 | 3 | 3 |
| Train station | inv9 | positive | 4 | 2 | 3 | 3 | 3 |
| Train station | inv9 | negative | 6 | 0 | 3 | 3 | 3 |
| Train station | inv10 | positive | 5 | 2 | 3 | 3 | 3 |
| Train station | inv10 | negative | 6 | 1 | 3 | 3 | 3 |
| Courses | inv1 | positive | 6 | 1 | 3 | 3 | 3 |
| Courses | inv1 | negative | 7 | 1 | 3 | 3 | 3 |
| Courses | inv2 | positive | 6 | 1 | 3 | 3 | 3 |
| Courses | inv2 | negative | 6 | 1 | 3 | 3 | 3 |
| Courses | inv3 | positive | 5 | 2 | 3 | 3 | 3 |
| Courses | inv3 | negative | 6 | 1 | 3 | 3 | 3 |
| Courses | inv4 | positive | 6 | 1 | 3 | 3 | 3 |
| Courses | inv4 | negative | 4 | 2 | 3 | 3 | 3 |
| Courses | inv5 | positive | 6 | 1 | 3 | 3 | 3 |
| Courses | inv5 | negative | 6 | 1 | 3 | 3 | 3 |
| Courses | inv6 | positive | 4 | 2 | 3 | 3 | 3 |
| Courses | inv6 | negative | 3 | 3 | 3 | 3 | 3 |
| Courses | inv7 | positive | 4 | 2 | 3 | 3 | 3 |
| Courses | inv7 | negative | 5 | 0 | 3 | 3 | 2 |
| Courses | inv8 | positive | 5 | 1 | 3 | 3 | 3 |
| Courses | inv8 | negative | 6 | 1 | 3 | 3 | 3 |
| Courses | inv9 | positive | 6 | 1 | 3 | 3 | 3 |
| Courses | inv9 | negative | 7 | 1 | 3 | 3 | 3 |
| Courses | inv10 | positive | 6 | 1 | 3 | 3 | 3 |
| Courses | inv10 | negative | 6 | 1 | 3 | 3 | 3 |
| Courses | inv11 | positive | 5 | 2 | 3 | 3 | 3 |
| Courses | inv11 | negative | 6 | 1 | 3 | 3 | 3 |
| Courses | inv12 | positive | 5 | 1 | 3 | 3 | 3 |
| Courses | inv12 | negative | 7 | 1 | 3 | 3 | 3 |
| Courses | inv13 | positive | 3 | 3 | 3 | 3 | 3 |
| Courses | inv13 | negative | 4 | 2 | 3 | 3 | 3 |
| Courses | inv14 | positive | 6 | 1 | 3 | 3 | 3 |
| Courses | inv14 | negative | 6 | 1 | 3 | 3 | 3 |
| Courses | inv15 | positive | 5 | 2 | 3 | 3 | 3 |
| Courses | inv15 | negative | 7 | 1 | 3 | 3 | 3 |

Class IDs, complete representative predicates, every command's class assignment, per-requirement pairwise statistics, and exclusions are available in the JSON report.
