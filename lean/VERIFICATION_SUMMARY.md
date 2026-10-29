# Lean verification: time and memory

One complete verification of all 117 rows, run with `tools/verify_catalogue.py` on 2026-10-28 and 2026-10-29 on the sources of this release. Every project module was compiled from source into an empty build directory, one Lean process at a time with one thread, under a 24 GiB memory cap (Lean heap `-M 22528`); the last step, the kernel-checked catalogue count, was then completed under a 32 GiB cap (see below). Mathlib (`fabf563`) was prebuilt.

- Toolchain: Lean 4.31.0
- Machine: Windows 11, 20 logical CPUs (only one used), 64 GiB RAM
- Result: 117/117 rows verified; every row theorem depends only on `propext`, `Classical.choice`, `Quot.sound`
- Total compile time 20:15:08, plus 0:14:46 of per-row axiom audits
- Largest peak memory 17.35 GiB (Atlas 145)
- The last step, the kernel-checked catalogue count (`Taeyoung.Catalogue.Counts`, 2 modules, 0:00:34), imports all 117 rows. Lean maps the `.olean` files of an import closure copy-on-write, and Windows charges every page of such a mapping to the process when the view is created, whether or not it is ever touched. For this step the mapped files come to 22.2 GiB (15.3 GiB of project `.olean` files plus Mathlib's) and the heap to 1.6 GiB, so the process shows 24.29 GiB of private memory while only 5.21 GiB is resident. It fails under a 24 GiB cap and passes under a 32 GiB cap.

Memory is the peak private memory of the Lean process as Windows accounts it: the heap plus the copy-on-write charge for the mapped `.olean` files of the module's imports, which is why it exceeds the resident memory. Times are wall-clock.

## Rows

**Alone** is the cost of verifying that row by itself from scratch: every module it imports, plus its audit. Rows share most of their imports, so the column does not add up to the total.

| Atlas | Status | Modules | Alone | Peak GiB |
|---:|---|---:|---:|---:|
| 7 | positive | 37 | 0:04:52 | 4.18 |
| 15 | positive | 19 | 0:02:26 | 3.51 |
| 17 | positive | 37 | 0:04:52 | 4.18 |
| 18 | positive | 37 | 0:04:52 | 4.18 |
| 34 | positive | 20 | 0:02:34 | 3.51 |
| 35 | positive | 49 | 0:06:44 | 4.20 |
| 36 | positive | 22 | 0:02:51 | 3.51 |
| 38 | positive | 18 | 0:02:44 | 7.82 |
| 40 | positive | 44 | 0:05:59 | 4.20 |
| 41 | positive | 49 | 0:06:44 | 4.20 |
| 42 | positive | 37 | 0:04:52 | 4.18 |
| 43 | positive | 1101 | 5:42:53 | 14.49 |
| 45 | positive | 32 | 0:04:21 | 4.16 |
| 46 | positive | 37 | 0:04:52 | 4.18 |
| 47 | positive | 37 | 0:04:52 | 4.18 |
| 48 | negative | 23 | 0:02:58 | 4.11 |
| 49 | positive | 33 | 0:04:20 | 4.16 |
| 50 | negative | 23 | 0:02:58 | 4.05 |
| 51 | positive | 37 | 0:04:52 | 4.18 |
| 52 | positive | 37 | 0:04:52 | 4.18 |
| 84 | positive | 29 | 0:03:44 | 4.13 |
| 92 | positive | 21 | 0:02:41 | 3.51 |
| 93 | positive | 49 | 0:06:44 | 4.20 |
| 94 | positive | 51 | 0:07:01 | 4.20 |
| 95 | positive | 46 | 0:06:15 | 4.20 |
| 97 | positive | 52 | 0:07:59 | 4.25 |
| 100 | positive | 51 | 0:07:45 | 4.24 |
| 102 | positive | 56 | 0:07:29 | 4.20 |
| 104 | positive | 25 | 0:05:32 | 7.89 |
| 106 | positive | 37 | 0:04:53 | 4.18 |
| 111 | positive | 44 | 0:05:58 | 4.20 |
| 112 | positive | 49 | 0:06:44 | 4.20 |
| 113 | positive | 52 | 0:07:22 | 4.21 |
| 114 | positive | 47 | 0:06:26 | 4.20 |
| 115 | positive | 48 | 0:06:32 | 4.20 |
| 117 | positive | 44 | 0:05:58 | 4.20 |
| 118 | positive | 338 | 2:03:28 | 11.40 |
| 119 | positive | 53 | 0:07:54 | 4.24 |
| 120 | positive | 48 | 0:06:36 | 4.20 |
| 122 | positive | 338 | 2:03:31 | 11.40 |
| 123 | positive | 49 | 0:06:45 | 4.20 |
| 124 | positive | 338 | 2:03:29 | 11.40 |
| 126 | positive | 176 | 0:54:04 | 8.80 |
| 127 | positive | 347 | 2:21:02 | 11.40 |
| 129 | negative | 21 | 0:03:36 | 15.15 |
| 130 | positive | 487 | 2:49:53 | 11.40 |
| 133 | positive | 32 | 0:04:09 | 4.16 |
| 134 | positive | 51 | 0:07:06 | 4.21 |
| 135 | positive | 44 | 0:05:58 | 4.20 |
| 136 | positive | 44 | 0:05:58 | 4.20 |
| 137 | positive | 51 | 0:07:03 | 4.21 |
| 138 | positive | 50 | 0:06:56 | 4.21 |
| 139 | positive | 51 | 0:07:03 | 4.21 |
| 140 | negative | 23 | 0:03:49 | 12.89 |
| 141 | negative | 23 | 0:04:03 | 15.65 |
| 142 | positive | 50 | 0:07:28 | 4.20 |
| 143 | negative | 23 | 0:03:53 | 13.75 |
| 144 | positive | 37 | 0:04:53 | 4.18 |
| 145 | positive | 55 | 0:11:41 | 17.35 |
| 147 | positive | 347 | 2:20:53 | 11.40 |
| 148 | positive | 54 | 0:10:38 | 17.13 |
| 149 | negative | 20 | 0:03:20 | 13.59 |
| 150 | positive | 37 | 0:04:53 | 4.18 |
| 151 | positive | 347 | 2:20:58 | 11.40 |
| 152 | negative | 23 | 0:04:26 | 14.48 |
| 153 | positive | 348 | 2:21:18 | 11.40 |
| 156 | positive | 33 | 0:04:20 | 4.16 |
| 157 | positive | 339 | 2:04:46 | 11.40 |
| 158 | negative | 23 | 0:03:50 | 12.97 |
| 159 | negative | 23 | 0:03:49 | 14.30 |
| 160 | positive | 53 | 0:08:55 | 4.25 |
| 161 | positive | 37 | 0:04:53 | 4.18 |
| 162 | positive | 37 | 0:04:53 | 4.18 |
| 163 | positive | 37 | 0:04:53 | 4.18 |
| 164 | positive | 37 | 0:04:53 | 4.18 |
| 165 | positive | 33 | 0:04:20 | 4.16 |
| 166 | negative | 22 | 0:03:36 | 12.61 |
| 167 | positive | 37 | 0:04:53 | 4.18 |
| 168 | positive | 347 | 2:20:56 | 11.40 |
| 169 | positive | 339 | 2:04:40 | 11.40 |
| 170 | negative | 20 | 0:03:20 | 13.50 |
| 171 | positive | 348 | 2:25:02 | 11.40 |
| 172 | negative | 22 | 0:03:40 | 12.46 |
| 173 | negative | 20 | 0:03:26 | 13.76 |
| 174 | positive | 348 | 2:24:21 | 11.40 |
| 177 | positive | 42 | 0:05:40 | 4.20 |
| 178 | positive | 55 | 0:08:12 | 4.20 |
| 179 | positive | 42 | 0:05:39 | 4.20 |
| 180 | positive | 49 | 0:06:45 | 4.20 |
| 181 | positive | 339 | 2:05:51 | 11.40 |
| 182 | negative | 20 | 0:03:15 | 12.50 |
| 183 | positive | 42 | 0:05:38 | 4.20 |
| 184 | negative | 20 | 0:03:11 | 11.78 |
| 185 | positive | 339 | 2:04:34 | 11.40 |
| 186 | negative | 20 | 0:03:19 | 13.22 |
| 187 | positive | 37 | 0:07:06 | 7.82 |
| 188 | positive | 348 | 2:22:53 | 11.40 |
| 189 | negative | 20 | 0:03:17 | 12.64 |
| 190 | negative | 20 | 0:03:16 | 12.48 |
| 191 | positive | 32 | 0:04:10 | 4.16 |
| 192 | positive | 44 | 0:05:58 | 4.20 |
| 193 | positive | 49 | 0:06:44 | 4.20 |
| 194 | positive | 339 | 2:06:20 | 11.40 |
| 195 | positive | 37 | 0:04:54 | 4.18 |
| 196 | positive | 1120 | 5:45:30 | 14.49 |
| 197 | negative | 20 | 0:03:09 | 10.88 |
| 198 | negative | 20 | 0:03:11 | 11.21 |
| 199 | positive | 339 | 2:05:46 | 11.40 |
| 200 | positive | 42 | 0:05:39 | 4.20 |
| 201 | positive | 37 | 0:04:54 | 4.18 |
| 202 | positive | 37 | 0:04:54 | 4.18 |
| 203 | positive | 488 | 2:54:30 | 11.40 |
| 204 | negative | 20 | 0:03:12 | 10.79 |
| 205 | positive | 42 | 0:05:40 | 4.20 |
| 206 | negative | 22 | 0:03:22 | 9.84 |
| 207 | positive | 37 | 0:04:54 | 4.18 |
| 208 | positive | 37 | 0:04:53 | 4.18 |

## Shared libraries

Each library imported by more than one row, compiled once.

| Library | Modules | Rows using it | Compile time | Peak GiB |
|---|---:|---:|---:|---:|
| Foundation | 15 | 117 | 0:01:48 | 3.47 |
| PureChordal | 23 | 91 | 0:03:07 | 4.18 |
| Link | 6 | 52 | 0:00:49 | 3.50 |
| Chromatic | 1 | 49 | 0:00:07 | 3.47 |
| RootedTriangleTree | 4 | 49 | 0:00:32 | 3.51 |
| PathSidorenko | 1 | 32 | 0:00:08 | 3.50 |
| GeometricMean | 1 | 6 | 0:00:08 | 3.47 |
| AffineProduct | 1 | 38 | 0:00:07 | 2.56 |
| CliqueLeaf | 4 | 44 | 0:00:35 | 4.16 |
| ConeBound | 1 | 41 | 0:00:09 | 4.13 |
| PawCone | 2 | 39 | 0:00:19 | 4.15 |
| Components | 1 | 37 | 0:00:10 | 4.13 |
| BaseCone | 2 | 38 | 0:00:20 | 4.20 |
| ForestCone | 1 | 30 | 0:00:11 | 4.20 |
| TwoRoot | 2 | 4 | 0:00:20 | 4.20 |
| OddCycleC5 | 2 | 3 | 0:00:30 | 7.82 |
| PageBook | 2 | 7 | 0:00:21 | 4.17 |
| Negative | 7 | 47 | 0:00:52 | 3.48 |
| RootedSOS: core | 188 | 21 | 0:55:48 | 8.58 |
| RootedSOS: Atlas 43 chain | 1076 | 2 | 5:39:50 | 14.49 |
| Peeling | 1 | 13 | 0:00:07 | 3.47 |
| BookTail | 1 | 11 | 0:00:10 | 3.51 |
| K4Tail | 3 | 7 | 0:01:02 | 4.18 |
| Broom | 1 | 2 | 0:00:19 | 4.24 |
| OddLeaf | 2 | 2 | 0:00:15 | 3.49 |
| CliqueDist | 2 | 2 | 0:00:24 | 4.21 |
| RootedSOS: CompactS4 | 48 | 19 | 0:42:14 | 11.40 |
| Atlas160 | 2 | 2 | 0:01:16 | 4.18 |
| Fisher | 17 | 3 | 0:04:05 | 7.85 |
| TriangleDensity | 2 | 4 | 0:00:20 | 7.79 |
| Atlas178 | 2 | 2 | 0:00:17 | 4.14 |
| RootedSOS: Induced | 137 | 2 | 0:37:45 | 10.85 |
| PagePawBranch | 2 | 4 | 0:00:20 | 4.21 |
| Atlas148 | 11 | 2 | 0:02:56 | 17.13 |
