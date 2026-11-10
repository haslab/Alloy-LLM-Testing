# Structural and fault-detection overlap between generated test runs

Tests are grouped separately for each benchmark, requirement, and intended polarity. Only satisfiable tests with an explicit expect 0/1 and a unique visible structure modulo atom renaming are compared. Each structure is encoded as a complete instance predicate I; another test P matches when P and I is satisfiable under P's original scopes and integer bitwidth. Signatures, fields, and ordering successors are preserved; integer/string values retain their identities. Skolem witnesses and private module implementation relations are ignored. Different commands encoding the same structure count once in overlap sets. No larger comparison scope is introduced.

Cohort: **consistent and unique**. Structural overlap includes consistent, unique tests even when they fail earlier requirements or have incorrect labels.
Validity is always checked afresh for the separate invalid-test recurrence section.

- **run1**: `/Users/alcino/Projectos/Alloy-LLM-Testing/results/fac27/claude-sonnet-5-5_claude-api_prompt_few_gpt_3pos-3neg_20261103-172111.json`
- **run2**: `/Users/alcino/Projectos/Alloy-LLM-Testing/results/fac27/claude-sonnet-5-5_claude-api_prompt_few_gpt_3pos-3neg_20261103-174824.json`
- **run3**: `/Users/alcino/Projectos/Alloy-LLM-Testing/results/fac27/claude-sonnet-5-5_claude-api_prompt_few_gpt_3pos-3neg_20261103-180936.json`

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

## Overlap in detected and missed specifications

Fault detection is compared only for requirements with a complete valid suite in every run. Requested counts come from generation metadata or recognized filenames, never generated counts. All runs use the same erroneous-specification catalogue and preceding requirement oracles. A specification is detected if at least one test disagrees with its expect annotation when that specification replaces the target oracle. Tests retain their original scopes and bitwidth. Exact duplicate specifications are counted once; IDs hash the benchmark, requirement, and specification text with leading/trailing whitespace removed. Unparseable specifications and specifications with an unassessed outcome in any run are excluded from every run's denominator and reported separately, never counted as missed. Empty set unions have no defined Jaccard. Primary averages weight requirements equally; pooled statistics are also provided. Agreement establishes discrimination against this fault catalogue, not scenario equivalence.

Requirements with complete valid suites and a shared catalogue: **38/43**. Requirements with at least one assessed specification: **38**. Assessed specifications: **4147**. Unparseable specifications excluded: **0**. Specifications with assessment gaps: **0**.

### Detection and benefit of combining runs

Coverage below is the unweighted mean of per-requirement detection rates on the shared assessed catalogue. Counts are pooled; they do not determine the mean coverage. `Only this run` counts specifications detected by that run and missed by every other run.

| Run | Detected | Missed | Only this run | Mean coverage |
| --- | ---: | ---: | ---: | ---: |
| run1 | 3787 | 360 | 26 | 92.99% |
| run2 | 3809 | 338 | 70 | 92.70% |
| run3 | 3772 | 375 | 46 | 92.09% |

Combined mean coverage: **96.16%**; best individual run: **92.99%**; gain: **3.17 percentage points**.

Pooled combined detection: **3942/4147**; best individual run: **3809**; additional specifications detected: **133**.

The combined result uses every test from every run and therefore a larger test budget. Mean coverage gain compares the combined suite with the best single run across the shared requirements, rather than selecting a different best run for each requirement.

### Pairwise overlap of detected and missed sets

Primary Jaccard values are averaged per requirement. The number of contributing requirements can differ between detected and missed sets because empty unions are undefined.

| Runs | Mean detected Jaccard | Requirements | Mean missed Jaccard | Requirements |
| --- | ---: | ---: | ---: | ---: |
| run1 / run2 | 94.80% | 38 | 49.65% | 37 |
| run1 / run3 | 95.02% | 38 | 49.52% | 37 |
| run2 / run3 | 93.96% | 38 | 45.83% | 37 |

Pooled overlap is also shown; requirements with more faulty specifications have more weight here.

| Runs | Detected shared | Detected union | Detected Jaccard | Left only | Right only | Missed shared | Missed union | Missed Jaccard |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| run1 / run2 | 3700 | 3896 | 94.97% | 87 | 109 | 251 | 447 | 56.15% |
| run1 / run3 | 3687 | 3872 | 95.22% | 100 | 85 | 275 | 460 | 59.78% |
| run2 / run3 | 3665 | 3916 | 93.59% | 144 | 107 | 231 | 482 | 47.93% |

**Detected in all runs:** 3626; **detected in any run:** 3942; mean all-run Jaccard: **91.98%** (38 requirements); pooled all-run Jaccard: **91.98%**.

**Missed in all runs:** 205; **missed in any run:** 521; mean all-run Jaccard: **33.14%** (37 requirements); pooled all-run Jaccard: **39.35%**.

### Fault detection per requirement

Per-requirement gain uses that requirement's best individual suite as its baseline.

| Benchmark | Requirement | Assessed faults | Best run | Combined | Gain | Gain (pp) | Detected Jaccard | Missed Jaccard |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Photo sharing social network | inv1 | 126 | 125 | 126 | 1 | 0.79 | 95.24% | 0.00% |
| Photo sharing social network | inv2 | 44 | 43 | 44 | 1 | 2.27 | 93.18% | 0.00% |
| Photo sharing social network | inv4 | 127 | 123 | 124 | 1 | 0.79 | 95.16% | 33.33% |
| Photo sharing social network | inv5 | 121 | 121 | 121 | 0 | 0.00 | 98.35% | 0.00% |
| Photo sharing social network | inv6 | 71 | 65 | 66 | 1 | 1.41 | 92.42% | 50.00% |
| Photo sharing social network | inv7 | 464 | 454 | 454 | 0 | 0.00 | 98.68% | 62.50% |
| Photo sharing social network | inv8 | 179 | 161 | 168 | 7 | 3.91 | 65.48% | 15.94% |
| Production line | inv1 | 50 | 47 | 50 | 3 | 6.00 | 86.00% | 0.00% |
| Production line | inv2 | 92 | 89 | 89 | 0 | 0.00 | 100.00% | 100.00% |
| Production line | inv3 | 31 | 31 | 31 | 0 | 0.00 | 100.00% | — |
| Production line | inv4 | 85 | 81 | 81 | 0 | 0.00 | 85.19% | 25.00% |
| Production line | inv5 | 66 | 65 | 65 | 0 | 0.00 | 95.38% | 25.00% |
| Production line | inv6 | 46 | 40 | 40 | 0 | 0.00 | 95.00% | 75.00% |
| Production line | inv7 | 78 | 72 | 75 | 3 | 3.85 | 85.33% | 21.43% |
| Production line | inv8 | 78 | 74 | 75 | 1 | 1.28 | 85.33% | 21.43% |
| Production line | inv9 | 647 | 540 | 553 | 13 | 2.01 | 94.21% | 74.60% |
| Production line | inv10 | 89 | 80 | 85 | 5 | 5.62 | 82.35% | 21.05% |
| Train station | inv1 | 134 | 129 | 130 | 1 | 0.75 | 95.38% | 40.00% |
| Train station | inv2 | 48 | 47 | 47 | 0 | 0.00 | 95.74% | 33.33% |
| Train station | inv3 | 122 | 121 | 122 | 1 | 0.82 | 95.08% | 0.00% |
| Train station | inv4 | 77 | 73 | 76 | 3 | 3.90 | 89.47% | 11.11% |
| Train station | inv7 | 20 | 20 | 20 | 0 | 0.00 | 95.00% | 0.00% |
| Train station | inv8 | 20 | 18 | 18 | 0 | 0.00 | 100.00% | 100.00% |
| Train station | inv9 | 143 | 139 | 141 | 2 | 1.40 | 95.04% | 22.22% |
| Train station | inv10 | 48 | 45 | 45 | 0 | 0.00 | 95.56% | 60.00% |
| Courses | inv1 | 166 | 163 | 166 | 3 | 1.81 | 90.36% | 0.00% |
| Courses | inv2 | 34 | 32 | 32 | 0 | 0.00 | 90.62% | 40.00% |
| Courses | inv3 | 65 | 61 | 65 | 4 | 6.15 | 86.15% | 0.00% |
| Courses | inv4 | 86 | 84 | 85 | 1 | 1.16 | 92.94% | 14.29% |
| Courses | inv5 | 205 | 181 | 192 | 11 | 5.37 | 86.46% | 33.33% |
| Courses | inv6 | 111 | 107 | 108 | 1 | 0.90 | 93.52% | 30.00% |
| Courses | inv7 | 109 | 105 | 107 | 2 | 1.83 | 83.18% | 10.00% |
| Courses | inv8 | 62 | 57 | 58 | 1 | 1.61 | 86.21% | 33.33% |
| Courses | inv10 | 69 | 66 | 66 | 0 | 0.00 | 100.00% | 100.00% |
| Courses | inv11 | 66 | 61 | 61 | 0 | 0.00 | 91.80% | 50.00% |
| Courses | inv12 | 54 | 54 | 54 | 0 | 0.00 | 96.30% | 0.00% |
| Courses | inv14 | 41 | 39 | 39 | 0 | 0.00 | 92.31% | 40.00% |
| Courses | inv15 | 73 | 62 | 63 | 1 | 1.37 | 96.83% | 83.33% |

### Requirements excluded from fault-detection comparison

Structural comparison and invalid-test recurrence still include these requirements.

| Benchmark | Requirement | Reason |
| --- | --- | --- |
| Photo sharing social network | inv3 | run2: suite is not complete and valid |
| Train station | inv5 | run3: suite is not complete and valid |
| Train station | inv6 | run3: suite is not complete and valid |
| Courses | inv9 | run1: suite is not complete and valid; run2: suite is not complete and valid; run3: suite is not complete and valid |
| Courses | inv13 | run1: suite is not complete and valid |

The JSON report includes stable specification IDs and source text, per-run detected/missed IDs, individual outcomes, per-requirement overlap and gains, and catalogue exclusions.

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
