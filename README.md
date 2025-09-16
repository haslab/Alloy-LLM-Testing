## Semantic grouping of entries

Script `semantic_grouping.py` groups together all entries of an Alloy4Fun database that have been submitted to given challenges. Entries are grouped when semantically equivalent according to the Alloy solver (i.e., equivalence within a certain scope). Since the solver is called to compare entries, this may take some time.

Two entries are equivalent for a challenge if the predicate to be filled by the student are equivalent (identified as an empty predicate called from a check command in the root model). This has a few consequences:
- This ignores any pre-condition in the check. This means that there may be multiple correct groups (which were equivalent under the pre-conditions).
- If the student used any auxiliary predicate, the test will fail, since these are not copied into the test (there are few cases, identified in the log).

The script only considers execution entries that are syntactically correct in the database (no sharing entries, nor errored). There are however some entries marked as executing successfully but still syntactically incorrect, unclear why.

### Usage

Start by installing the requirements.

```
pip install -r requirements.txt
```

Then run the script as:

```
usage: semantic_grouping.py [-h] [-o OUTPUT] [-s SCOPE] jar entries ...

Script for grouping semantically equivalent Alloy entries

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

### Results

Script was run for models Social Network (`x3JXgWhJ3uti5Dzxz`), Courses (`iP5JL36afv5KbDKP6`), Production line (`dyj49tEp7j6aWAQQX`) and Train Station (`cXPP9QBPTYgTX6WJ6`) with scope 3. Statistics are [here](results/log.txt) and groups in [results folder](results). Note: takes a few hours to run.

