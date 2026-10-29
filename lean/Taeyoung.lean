import Taeyoung.Catalogue.Counts
import Taeyoung.Paper
import Taeyoung.Paper.Refinements

/-!
# Goodman-type lower bounds for graph homomorphism densities

The Lean development accompanying `paper.pdf`.  The default target imports

* `Taeyoung.Catalogue.Counts`: Theorem 1.7, the
  classification of the `117` nonbipartite graphs on at most six vertices with
  no isolated vertices and no `K₂` component.  Each graph has a module
  `Taeyoung.Examples.GraphNNN` (`NNN` its number in the Graph Atlas) whose
  theorem `status` is `SatisfiesLowerBound graph` or `ViolatesLowerBound graph`;
  `Catalogue/Counts.lean` checks in the kernel that `94` rows are positive,
  `23` negative, and all are verified;
* `Taeyoung.Paper`: the general theorems of the paper.  Its header maps each
  result, by label, to the Lean declaration that proves it.
* `Taeyoung.Paper.Refinements`: Section 5.1 — for each of the 23
  violating graphs, the density range on which the bound still holds and the
  integers `k` at which `T_k` is or is not optimal (Table 1).

## Layout

* `Foundation/`: graphons, homomorphism densities, chromatic polynomials, the
  target `Φ_H` (`chromaticTarget`) and the predicates `SatisfiesLowerBound`,
  `ViolatesLowerBound`.
* `Methods/`: the proof methods used by the catalogue rows, including the
  exact rational sum-of-squares certificates (`Methods/RootedSOS/`) and the
  explicit counterexamples (`Methods/Negative/`).
* `Fisher/`: Fisher's sharp triangle-density bound on `1/2 < p ≤ 2/3`, used by
  Atlas 126, 145 and 148 through `Methods/TriangleDensity/Fisher.lean`.
* `Examples/`, `Catalogue/`: the catalogue rows and the row list.
* `Paper/`: the paper's theorems.
* `CheckPaper.lean`, `CheckRefinements.lean`, `CheckAtlas43.lean`: axiom audits of
  the paper's general results, of Table 1, and of the Atlas 43
  certificate chain, built on request.  The catalogue rows are
  audited one by one by `tools/verify_catalogue.py`.

The odd-cycle Goodman bound and the spectral theory of the graphon operator
come from the Lake dependency `OddCycleBound`, the formalization by Im, Kim,
and Yang (<https://github.com/mekty2012/OddCycleGoodman-lean>).

Several modules need 13–17 GiB of memory each (the Atlas 43 chain about
15 GiB), so a parallel `lake build` can run out of memory; `tools/README.md`
describes the sequential, memory-capped verification.
-/
