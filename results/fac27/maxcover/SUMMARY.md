# Optimal test-suite detection rates

Status: **completed**. Updated: 2026-11-03T00:55:37+00:00.

Dataset: [saved dataset](dataset.json); source: [source/](source/).
Solver: SAT4JMax. Cumulative requirements. Bound: 4 atoms per top-level domain. Each n requests n positive and n negative, structurally distinct tests.

Rates use parseable wrong specs as the denominator. Counts are obtained in Java, without Alloy's cardinality operator. Higher n are skipped only after exact 100% coverage, zero parseable specs, or proven suite infeasibility. Errors/timeouts leave higher n blocked, never reported as optimal.

Cases: optimal: 94, skipped_100_percent: 121.

See [results.csv](results.csv) for timings, totals, skipped counts, and artifact paths; [results.json](results.json) also records input hashes, commands, and errors.

Invariants reaching 100% at n or earlier (counts are lower bounds while cases remain unresolved):

| n | Reached 100% | Unresolved | Infeasible |
|---:|---:|---:|---:|
| 1 | 9 | 0 | 0 |
| 2 | 32 | 0 | 0 |
| 3 | 39 | 0 | 0 |
| 4 | 41 | 0 | 0 |
| 5 | 42 | 0 | 0 |

| Example | Invariant (R) | Dataset total | Unparseable | n=1 | n=2 | n=3 | n=4 | n=5 |
|---|---|---:|---:|---|---|---|---|---|
| socialnetwork | inv1 (0) | 126 | 0 | 96.03% (121/126) | 100.00% (126/126) | — (100% at n=2) | — (100% at n=2) | — (100% at n=2) |
| socialnetwork | inv2 (1) | 44 | 0 | 100.00% (44/44) | — (100% at n=1) | — (100% at n=1) | — (100% at n=1) | — (100% at n=1) |
| socialnetwork | inv3 (2) | 613 | 0 | 99.18% (608/613) | 99.84% (612/613) | 100.00% (613/613) | — (100% at n=3) | — (100% at n=3) |
| socialnetwork | inv4 (3) | 127 | 0 | 97.64% (124/127) | 100.00% (127/127) | — (100% at n=2) | — (100% at n=2) | — (100% at n=2) |
| socialnetwork | inv5 (4) | 121 | 0 | 98.35% (119/121) | 100.00% (121/121) | — (100% at n=2) | — (100% at n=2) | — (100% at n=2) |
| socialnetwork | inv6 (5) | 71 | 0 | 92.96% (66/71) | 98.59% (70/71) | 100.00% (71/71) | — (100% at n=3) | — (100% at n=3) |
| socialnetwork | inv7 (6) | 464 | 0 | 97.41% (452/464) | 99.57% (462/464) | 99.78% (463/464) | 100.00% (464/464) | — (100% at n=4) |
| socialnetwork | inv8 (7) | 179 | 0 | 100.00% (179/179) | — (100% at n=1) | — (100% at n=1) | — (100% at n=1) | — (100% at n=1) |
| productionline | inv1 (0) | 50 | 0 | 98.00% (49/50) | 100.00% (50/50) | — (100% at n=2) | — (100% at n=2) | — (100% at n=2) |
| productionline | inv2 (1) | 92 | 0 | 90.22% (83/92) | 96.74% (89/92) | 97.83% (90/92) | 98.91% (91/92) | 100.00% (92/92) |
| productionline | inv3 (2) | 31 | 0 | 96.77% (30/31) | 100.00% (31/31) | — (100% at n=2) | — (100% at n=2) | — (100% at n=2) |
| productionline | inv4 (3) | 85 | 0 | 91.76% (78/85) | 100.00% (85/85) | — (100% at n=2) | — (100% at n=2) | — (100% at n=2) |
| productionline | inv5 (4) | 66 | 0 | 96.97% (64/66) | 100.00% (66/66) | — (100% at n=2) | — (100% at n=2) | — (100% at n=2) |
| productionline | inv6 (5) | 46 | 0 | 93.48% (43/46) | 100.00% (46/46) | — (100% at n=2) | — (100% at n=2) | — (100% at n=2) |
| productionline | inv7 (6) | 78 | 0 | 97.44% (76/78) | 100.00% (78/78) | — (100% at n=2) | — (100% at n=2) | — (100% at n=2) |
| productionline | inv8 (7) | 78 | 0 | 96.15% (75/78) | 100.00% (78/78) | — (100% at n=2) | — (100% at n=2) | — (100% at n=2) |
| productionline | inv9 (8) | 647 | 0 | 74.03% (479/647) | 91.19% (590/647) | 94.44% (611/647) | 96.45% (624/647) | 97.53% (631/647) |
| productionline | inv10 (9) | 89 | 0 | 95.51% (85/89) | 100.00% (89/89) | — (100% at n=2) | — (100% at n=2) | — (100% at n=2) |
| trainstation | inv1 (0) | 134 | 0 | 95.52% (128/134) | 99.25% (133/134) | 100.00% (134/134) | — (100% at n=3) | — (100% at n=3) |
| trainstation | inv2 (1) | 48 | 0 | 95.83% (46/48) | 100.00% (48/48) | — (100% at n=2) | — (100% at n=2) | — (100% at n=2) |
| trainstation | inv3 (2) | 122 | 0 | 95.08% (116/122) | 99.18% (121/122) | 100.00% (122/122) | — (100% at n=3) | — (100% at n=3) |
| trainstation | inv4 (3) | 77 | 0 | 98.70% (76/77) | 100.00% (77/77) | — (100% at n=2) | — (100% at n=2) | — (100% at n=2) |
| trainstation | inv5 (4) | 136 | 0 | 94.12% (128/136) | 100.00% (136/136) | — (100% at n=2) | — (100% at n=2) | — (100% at n=2) |
| trainstation | inv6 (5) | 52 | 0 | 100.00% (52/52) | — (100% at n=1) | — (100% at n=1) | — (100% at n=1) | — (100% at n=1) |
| trainstation | inv7 (6) | 20 | 0 | 85.00% (17/20) | 95.00% (19/20) | 100.00% (20/20) | — (100% at n=3) | — (100% at n=3) |
| trainstation | inv8 (7) | 20 | 0 | 90.00% (18/20) | 100.00% (20/20) | — (100% at n=2) | — (100% at n=2) | — (100% at n=2) |
| trainstation | inv9 (8) | 143 | 0 | 95.80% (137/143) | 99.30% (142/143) | 100.00% (143/143) | — (100% at n=3) | — (100% at n=3) |
| trainstation | inv10 (9) | 48 | 0 | 91.67% (44/48) | 100.00% (48/48) | — (100% at n=2) | — (100% at n=2) | — (100% at n=2) |
| courses | inv1 (0) | 166 | 0 | 98.80% (164/166) | 100.00% (166/166) | — (100% at n=2) | — (100% at n=2) | — (100% at n=2) |
| courses | inv2 (1) | 34 | 0 | 97.06% (33/34) | 100.00% (34/34) | — (100% at n=2) | — (100% at n=2) | — (100% at n=2) |
| courses | inv3 (2) | 65 | 0 | 96.92% (63/65) | 100.00% (65/65) | — (100% at n=2) | — (100% at n=2) | — (100% at n=2) |
| courses | inv4 (3) | 86 | 0 | 97.67% (84/86) | 98.84% (85/86) | 100.00% (86/86) | — (100% at n=3) | — (100% at n=3) |
| courses | inv5 (4) | 205 | 0 | 92.68% (190/205) | 98.54% (202/205) | 99.51% (204/205) | 100.00% (205/205) | — (100% at n=4) |
| courses | inv6 (5) | 111 | 0 | 99.10% (110/111) | 100.00% (111/111) | — (100% at n=2) | — (100% at n=2) | — (100% at n=2) |
| courses | inv7 (6) | 109 | 0 | 100.00% (109/109) | — (100% at n=1) | — (100% at n=1) | — (100% at n=1) | — (100% at n=1) |
| courses | inv8 (7) | 62 | 0 | 96.77% (60/62) | 100.00% (62/62) | — (100% at n=2) | — (100% at n=2) | — (100% at n=2) |
| courses | inv9 (8) | 152 | 0 | 100.00% (152/152) | — (100% at n=1) | — (100% at n=1) | — (100% at n=1) | — (100% at n=1) |
| courses | inv10 (9) | 69 | 0 | 100.00% (69/69) | — (100% at n=1) | — (100% at n=1) | — (100% at n=1) | — (100% at n=1) |
| courses | inv11 (10) | 66 | 0 | 98.48% (65/66) | 100.00% (66/66) | — (100% at n=2) | — (100% at n=2) | — (100% at n=2) |
| courses | inv12 (11) | 54 | 0 | 100.00% (54/54) | — (100% at n=1) | — (100% at n=1) | — (100% at n=1) | — (100% at n=1) |
| courses | inv13 (12) | 206 | 0 | 98.06% (202/206) | 100.00% (206/206) | — (100% at n=2) | — (100% at n=2) | — (100% at n=2) |
| courses | inv14 (13) | 41 | 0 | 100.00% (41/41) | — (100% at n=1) | — (100% at n=1) | — (100% at n=1) | — (100% at n=1) |
| courses | inv15 (14) | 73 | 0 | 100.00% (73/73) | — (100% at n=1) | — (100% at n=1) | — (100% at n=1) | — (100% at n=1) |
