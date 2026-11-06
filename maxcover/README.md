Run from any working directory (with Java and JPype installed):

```sh
python minimal/optimal.py EXAMPLE R [n] --scope 4 --solver z3
```

`--scope S` sets the maximum number of atoms per top-level domain in each test
(default **4**). `--solver sat4jmax` uses the bundled Java optimizer (the default);
`--solver z3` uses Z3 Optimize while retaining Alloy's concrete instance decoding.
Z3 mode requires the Python `z3-solver` package and a JDK to compile a small cached
adapter against the pinned AlloyMax JAR. The JAR is not modified. Both backends
print the same complete scenario format and count `detected` through Java.

The four example names are `socialnetwork`, `productionline`, `trainstation`,
and `courses`. Each also has a convenience script with the same arguments as
the original social-network script:

```sh
python minimal/socialnetwork.py 0 2
python minimal/productionline.py 2 1
python minimal/trainstation.py 4 1
python minimal/courses.py 12 1
# Equivalent to the last command:
python minimal/optimal.py courses 12 1
```

`R` is the **zero-based** requirement index: 0–7 for Social Network, 0–9 for
Production Line and Train Station, and 0–14 for Courses. Thus Courses `inv8`
is `R=7`, and `inv9` is `R=8`. `n` defaults to one and requests **n positive
and n negative** tests, with exactly `2*n` `Instance` atoms internally.
Requirements are cumulative: every positive and negative test satisfies the
oracles of requirements `0..R-1` as hard constraints.

All scripts default to **`prepare/results/dataset.json`**, using both its
oracles and its wrong specifications. Social Network requirement 0 now has
119 wrong specifications; this differs from the 118 in the earlier study
snapshot. Output identifies the dataset path. `--dataset` can select another
snapshot with the same model declarations.

`optimal.py` shares the solver, suite construction, totals, and output.
`benchmarks.py` explicitly encodes the declarations of these four examples,
including multiplicities, abstract signatures, overlapping subsets, disjoint
extensions, and field types. This is not a translator for arbitrary Alloy
models; unsupported declarations are rejected. References in specifications
are resolved by Alloy's parser before reification, including the two overloaded
Courses `projects` fields and `util/ordering` functions. Each instance has its
own universe and identity relation, including for reflexive closure.

The bound is **at most `--scope` atoms per top-level domain signature**, per test
(default four).
Separate typed pools tighten the search without forcing every slot to occur in
a test. Descendants share their parent's bound: Production Line has at most
`--scope` Products in total, split between Material and Component. Singleton
subsets `begin` and `end` each contain one Workstation and may coincide.
Train Station's `Junction`, `Entry`, and `Exit` subsets may overlap.

Courses has at most `--scope` Persons, Courses, Projects, and Grades. Grades are
nonempty and form a total order, with **one to `--scope`** actual grades per test.
Output specifies the exact Grade scope and the entire `Grade <: next` chain,
both overloaded `projects` relations, and the ternary `grades` relation.
Internally, grades are stored as `--scope` binary tables, one per possible Course,
to avoid AlloyMax's capacity limit for four-column reified relations; their
union supplies the original ternary relation to every specification.
Integer bitwidth covers the bounded domain relation cardinalities and requested
suite size; it is never used to count detected specifications.

**Prepared dataset caveat:** Courses `inv9` (`R=8`, “A professor cannot teach
colleagues”) also has a comment-only oracle in `prepare/results/dataset.json`.
That oracle is true, so no negative test exists for it. The script reports
infeasibility for `n > 0`; it does not substitute a different oracle.

The script executes the adjacent `AlloyMax-1.0.2.jar` through JPype using its
Java SAT4JMax optimizer. It maximizes the number of benchmark wrong specifications
whose classification differs from the supplied oracle on at least one test.
Each specification is counted once, and the oracle is excluded from `detected`.
The total is obtained using `solution.eval(detected).size()` in Java, without
Alloy cardinality arithmetic. The ratio is detected / parseable wrong specs.

Standard output contains complete concrete `PositiveScenario` and
`NegativeScenario` predicates, corresponding `run` commands with exact domain
scopes and `expect 1`/`expect 0`, and totals in Alloy comments. Append it to the
chosen example's declarations and earlier requirement facts. Both
classes satisfy those declarations and background facts; negative tests become
unsatisfiable when the target oracle is also enforced as a fact. Isomorphic
repetitions are excluded and the model is reoptimized
until the suite contains distinct structures. If the requested suite cannot
exist within the bounds, execution fails explicitly.

For example, generate two positive and two negative tests for requirement 0:

```sh
python minimal/socialnetwork.py 0 2 > suite.als
```

Progress goes to standard error. To also retain the optimization model:

```sh
python minimal/socialnetwork.py 0 2 --model-output optimization.als > suite.als
```

To export the optimization problem for Z3 instead of running SAT4JMax:

```sh
python minimal/socialnetwork.py 2 1 --export-z3 req2.smt2
z3 req2.smt2
```

This creates **both** `req2.wcnf` (weighted DIMACS, retaining hard clauses and
the MaxSAT objective) and `req2.smt2` (SMT-LIB with Z3 `assert-soft` commands).
Ordinary unweighted DIMACS would lose the objective. Z3 prints the satisfiability
status followed by `detected_count`, the maximum number of detected parseable
wrong specifications. The count uses integer arithmetic in Z3, independent of
Alloy's bitwidth. The files include the dataset totals, skipped count, suite
size, and number of earlier requirement facts as comments.

Exporting needs Java and JPype, with no Python Z3 dependency. It performs plain
satisfiability checks, but does not optimize the detection count; the script's
summary explicitly leaves the maximum uncomputed until Z3 is run. Add
`--model-output optimization.als` to retain the corresponding AlloyMax source.
An output prefix without `.smt2` is also accepted.

For `n > 1`, export first checks that `n` structurally distinct tests of each
class exist. The exported Boolean assignment may repeat structures, but its
optimal detection count is attainable with distinct tests: redundant copies
can be replaced without losing any original detection witness. The normal
mode constructs and prints the distinct concrete test suite.

`--jar` and `--dataset` override the default paths. Specifications that cannot
be parsed are skipped. The output reports the total wrong specifications in
the dataset, the number skipped, and the maximum detected out of the remaining
parseable specifications. The detection ratio uses the parseable count as its
denominator; it is N/A if no specifications can be parsed. The bundled
AlloyMax uses Alloy 5, so some specifications accepted by Alloy 6 are skipped.
Parse failures are reported separately from undetected specifications.

Run the solver integration checks with:

```sh
python -m unittest discover -s minimal -v
```

The optional export checks also use `z3-solver` when it is installed.

To measure every invariant in all four examples for `n = 1..5`:

```sh
python minimal/run_rates.py --output minimal/results/detection-rates --scope 4 --solver z3 --jobs 2
```

The runner stops an invariant as soon as its **exact** detected count equals
the number of parseable wrong specifications. A plateau below 100% does not
stop the run. Proven infeasibility stops higher sizes too; errors or optional
timeouts block higher sizes and are clearly distinguished from optimal results.
By default there is no time limit per case. `--timeout SECONDS` adds one, and
`--max-n N` changes the largest requested size.

Results are checkpointed throughout the run:

- `SUMMARY.md`: one row per invariant, with detection rates for each size.
- `results.csv`: exact counts, ratios, elapsed seconds, statuses, and artifact paths.
- `results.json`: the same results plus input hashes, commands, and run metadata.
- `cases/EXAMPLE/invK/`: concrete suites, optimization models, and solver logs.
- `dataset.json` and `source/`: frozen inputs used by this run.

Two independent cases run concurrently by default. Every invariant starts at
`n=1`, with larger sizes queued after the initial cases. The table uses both
the benchmark's one-based `invK` identifier and the zero-based requirement `R`.
All ratios use the parseable-specification denominator; the original dataset
total and skipped count remain visible. Empty-oracle and other infeasible cases
are recorded as such, with no detection rate invented for them.

To resume an interrupted batch using its saved inputs and completed results:

```sh
python minimal/run_rates.py --output minimal/results/detection-rates --scope 4 --solver z3 --resume
```

Add `--retry-failed` to also retry errors/timeouts. Attempts use separate artifact
filenames. A directory lock prevents two runners writing the same results.
After an optimizer fix, `--resume --retry-failed --refresh-source` adopts the
current source, archives the previous version in `source-history/`, and records
the source revision used for each result. The saved dataset stays unchanged.

With `--solver z3 --model-output problem.als`, each case also saves the weighted
DIMACS (`problem.wcnf`), corresponding SMT-LIB (`problem.smt2`), and Z3 statistics
(`problem.z3.json`). The adapter checks the returned assignment against every
hard clause before Alloy decodes it. Unknown/interrupted Z3 results are errors,
never reported as a proved optimum. Distinctness refinement applies equally to
both backends. The CLI counts detected specifications with Java's tuple-set size;
the exported SMT-LIB count uses Z3 integer arithmetic.

Scope and solver are recorded in batch metadata and CSV rows. Resume requires
matching `--scope` and `--solver` values; use a separate output directory to compare
bounds/backends. Scope 3 results remain reproducible with `--scope 3`.
