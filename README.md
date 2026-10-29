# Goodman-type lower bounds for graph homomorphism densities

This repository accompanies the paper

> Taeyoung Kim, *Goodman-type lower bounds for graph homomorphism densities* ([paper.pdf](paper.pdf)).

It contains the paper, the Lean 4 development ([lean/](lean/)) that formally verifies its main results, and the notes ([notes/](notes/)) that write up the graph-specific proofs behind the classification. The verified results are the theorems on chordal graphs, trivially perfect graphs, clique joins of odd cycles, and eventual validity by girth, together with the classification of the 117 nonbipartite graphs on at most six vertices and the density ranges for the 23 graphs that violate the bound. This file explains what is proved, where to find each statement in Lean, what the trusted base is, and how to check everything yourself.

## The inequality

For a finite graph $H$ with $v(H)$ vertices, chromatic number $\chi(H)$ and chromatic polynomial $P_H$, let

$$
\Phi_H(p)=(1-p)^{v(H)}\,P_H\!\left(\frac1{1-p}\right).
$$

This polynomial interpolates the homomorphism densities of $H$ in the balanced complete $k$-partite graphons $T_k$, since $t(H,T_k)=\Phi_H(1-1/k)$. The graph $H$ *satisfies the Goodman-type lower bound* if every graphon $W$ of edge density $p=t(K_2,W)$ satisfies

$$
t(H,W)\ \ge\ \Phi_H(p)\qquad\text{whenever}\qquad p>1-\frac1{\chi(H)-1}.
$$

For $H=K_3$ this is Goodman's inequality $t(K_3,W)\ge p(2p-1)$.

In Lean the inequality is the predicate `Taeyoung.SatisfiesLowerBound H` in [lean/Taeyoung/Foundation/Status.lean](lean/Taeyoung/Foundation/Status.lean). It quantifies over graphons on an arbitrary probability space, over every polynomial and every natural number satisfying the defining specifications of the chromatic polynomial and chromatic number, and over the closed range $p\ge 1-1/(\chi(H)-1)$, which is slightly stronger than the paper's open range. `ViolatesLowerBound H` is its negation.

## Results verified in Lean

| Paper | Statement | Lean declaration | File |
|---|---|---|---|
| Theorem 1.1 | A connected chordal graph whose maximal cliques all have the same size $k\ge3$ satisfies the bound. | `Taeyoung.Methods.PureChordal.pureChordal_satisfiesLowerBound` | [Methods/PureChordal/Main.lean](lean/Taeyoung/Methods/PureChordal/Main.lean) |
| Lemma 1.2 | The clique-tree criterion $b_1\le b_2\le\cdots\le b_k$. | `Taeyoung.Paper.Profile.chordal_satisfiesLowerBound_of_profile` | [Paper/Profile/Main.lean](lean/Taeyoung/Paper/Profile/Main.lean) |
| Proposition 2.1 | The entropy gluing inequality along a clique tree. | `Taeyoung.Paper.Profile.gluing_inequality` | [Paper/Profile/Main.lean](lean/Taeyoung/Paper/Profile/Main.lean) |
| Lemmas 2.2, 2.3 | The Moon–Moser recurrence and the clique-density step. | `Taeyoung.Methods.PureChordal.cliqueDensity_moonMoser_succ`, `cliqueDensity_step_lower` | [Methods/PureChordal/MoonMoser.lean](lean/Taeyoung/Methods/PureChordal/MoonMoser.lean), [Methods/PureChordal/CliquePolynomialBound.lean](lean/Taeyoung/Methods/PureChordal/CliquePolynomialBound.lean) |
| Theorem 1.3 | Every trivially perfect graph with an edge satisfies the bound. | `Taeyoung.Paper.IsTriviallyPerfect.satisfiesLowerBound` | [Paper/TriviallyPerfect.lean](lean/Taeyoung/Paper/TriviallyPerfect.lean) |
| Theorem 1.4 | Odd cycles: $t(C_\ell,W)\ge p^\ell-p(1-p)^{\ell-1}$ (Im, Kim, and Yang). | `Taeyoung.Paper.oddCycle_bound`, `cycleGraph_satisfiesLowerBound`, from `OddCycleBound.odd_cycle_bound` | [Paper/OddCycles.lean](lean/Taeyoung/Paper/OddCycles.lean) |
| Corollary 1.5 | Clique joins $K_s\vee C_\ell$ of odd cycles satisfy the bound. | `Taeyoung.Paper.oddJoin_satisfiesLowerBound` | [Paper/OddCycles.lean](lean/Taeyoung/Paper/OddCycles.lean) |
| Lemma 3.1 | The weighted rooted-triangle inequality. | `Taeyoung.Methods.Link.weighted_rootedTriangle` | [Methods/Link/WeightedGoodman.lean](lean/Taeyoung/Methods/Link/WeightedGoodman.lean) |
| Proposition 3.2 | Adding a universal vertex preserves the bound under the convexity hypothesis; its iteration. | `Taeyoung.Paper.lifting`, `iterated_lifting` | [Paper/Lifting.lean](lean/Taeyoung/Paper/Lifting.lean) |
| Theorem 1.6 | A nonbipartite graph eventually satisfies the bound if and only if its girth is odd; the bound holds for $p\ge 1-(72\,v(H)^{12})^{-1}$. | `Taeyoung.Paper.Eventual.eventual_tfae_of_not_bipartite`, `satisfiesLowerBoundOn_threshold`, `turanOptimal_of_odd_girth` | [Paper/Eventual/Main.lean](lean/Taeyoung/Paper/Eventual/Main.lean) |
| Theorem 4.7, Proposition 4.17 | The spectral cycle comparison; the obstruction for even girth. | `Taeyoung.Paper.Eventual.cycle_comparison`, `not_turanOptimal_of_even_girth` | [Paper/Eventual/Spectral.lean](lean/Taeyoung/Paper/Eventual/Spectral.lean), [Paper/Eventual/EvenGirth.lean](lean/Taeyoung/Paper/Eventual/EvenGirth.lean) |
| Theorem 1.7 | Of the 117 nonbipartite graphs on at most six vertices without isolated vertices or isolated edges, 94 satisfy the bound and 23 violate it. | `Taeyoung.Examples.GraphNNN.status` for each graph; the counts `Taeyoung.Catalogue.row_count`, `positive_count`, `negative_count` | [Examples/](lean/Taeyoung/Examples/), [Catalogue/Counts.lean](lean/Taeyoung/Catalogue/Counts.lean) |
| Table 1 | Density ranges on which the 23 violating graphs satisfy the bound, and the integers $k$ at which $T_k$ is or is not optimal. | `Taeyoung.Paper.Refinements.GraphNNN.lowerBoundRange`, `turanOptimal`, `not_turanOptimal_three` (`_four`, `_five`) | [Paper/Refinements/](lean/Taeyoung/Paper/Refinements/) |
| Section 5.2 | The counterexample constructions: $T_{2k-1}\otimes T_{2k}$, the constant graphon, and the three-, four- and five-part step graphons. | `Taeyoung.Methods.Negative.*`, used by the negative rows and by `Paper/Refinements/` | [Methods/Negative/](lean/Taeyoung/Methods/Negative/) |
| Proposition 6.1 | The chordal graph $L_{20}$ violates the bound. | `Taeyoung.Paper.leafTriangle_twenty_violates` | [Paper/ChordalLeaves.lean](lean/Taeyoung/Paper/ChordalLeaves.lean) |
| (1.3), (1.4) | The Turán values $t(H,T_k)=\Phi_H(1-1/k)$, and optimality of $T_k$ for every $k\ge\chi(H)$ when the bound holds. | `Taeyoung.Paper.homDensity_turan_eq_chromaticTarget`, `turanOptimal_of_satisfiesLowerBound` | [Paper/Turan.lean](lean/Taeyoung/Paper/Turan.lean) |

The header of [lean/Taeyoung/Paper.lean](lean/Taeyoung/Paper.lean) maps every labelled statement of the paper, including the lemmas of Section 4, to its Lean declaration, and lists the few lemmas that are proved in a different form or not separately. Of equation (5.1), the lower bound $14056671/200000000$ for graph 173 at $p=3/4$ is not formalized; it is a seven-point flag-algebra certificate checked outside Lean. The Lean counterexamples for the two families that the paper takes with $\varepsilon$ sufficiently small use $\varepsilon=1/3000$ (graph 152) and $\varepsilon=1/100$ (graph 190 at $k=4$).

The odd-cycle theorem (Theorem 1.4) and the spectral theory of the graphon operator used in Theorem 4.7 come from the Lake dependency `OddCycleBound`, the formalization by Im, Kim, and Yang that accompanies their paper (arXiv:2610.18277), at <https://github.com/mekty2012/OddCycleGoodman-lean>. [Paper/OddCycles.lean](lean/Taeyoung/Paper/OddCycles.lean) and [Paper/Eventual/Spectral.lean](lean/Taeyoung/Paper/Eventual/Spectral.lean) bridge its definitions to the ones used here.

## Layout of the Lean development

All sources are in [lean/Taeyoung/](lean/Taeyoung/), in the Lake package `TaeyoungVerification` with the single library `Taeyoung`.

| Path | Contents |
|---|---|
| [Foundation/](lean/Taeyoung/Foundation/) | Graphons on an arbitrary probability space, homomorphism densities, the chromatic polynomial and chromatic number by their defining properties, the target $\Phi_H$ (`chromaticTarget`), the predicates `SatisfiesLowerBound` and `ViolatesLowerBound`, and tools for relabelling, isomorphism, disjoint unions and links. |
| [Methods/](lean/Taeyoung/Methods/) | The proof methods used by the catalogue. `PureChordal/` proves Theorem 1.1 from clique trees; `Link/` proves the weighted rooted-triangle inequality; `BaseCone`, `ConeBound`, `ForestCone`, `PawCone`, `OddCycleCone` and the leaf, tail, book and page modules are the integral estimates for individual graphs, which fix one or more vertex positions and apply the triangle inequality, moment bounds, Cauchy–Schwarz and Jensen. `Atlas126/`, `Atlas145`, `Atlas148/`, `Atlas160/`, `Atlas178/` treat single graphs. |
| [Methods/RootedSOS/](lean/Taeyoung/Methods/RootedSOS/) | Exact rational sum-of-squares certificates, checked coefficient by coefficient with `decide +kernel`: the chain of about 1,100 modules for graph 43 (reused by graph 196), the compact four-root certificates in `CompactS4/` for 19 graphs, the induced certificates in `Induced/`, and in `Refinement/` the 24 six-point certificates behind Table 1. |
| [Methods/Bernstein/](lean/Taeyoung/Methods/Bernstein/) | Bernstein certificates of polynomial nonnegativity on intervals and boxes, with integer coefficients. |
| [Methods/Negative/](lean/Taeyoung/Methods/Negative/) | The counterexamples: step graphons on finite weighted spaces, the Turán tensor graphons $T_a\otimes T_b$, and the proper-colouring counts that give each graph its chromatic polynomial, all evaluated by kernel computation. |
| [Fisher/](lean/Taeyoung/Fisher/), [Methods/TriangleDensity/](lean/Taeyoung/Methods/TriangleDensity/) | Fisher's sharp triangle-density bound on $1/2<p\le2/3$, used by graphs 126, 145 and 148. |
| [Examples/](lean/Taeyoung/Examples/) | The 117 catalogue rows, one module `GraphNNN.lean` per graph, where `NNN` is its number in the Graph Atlas. |
| [Catalogue/](lean/Taeyoung/Catalogue/) | `Rows.lean` imports every row and lists their metadata; `Counts.lean` checks in the kernel that there are 117 rows, 94 positive and 23 negative, all verified. |
| [Paper/](lean/Taeyoung/Paper/) | The general theorems of the paper, and in `Refinements/` the rows of Table 1. |
| [CheckPaper.lean](lean/Taeyoung/CheckPaper.lean), [CheckRefinements.lean](lean/Taeyoung/CheckRefinements.lean), [CheckAtlas43.lean](lean/Taeyoung/CheckAtlas43.lean) | Axiom audits: one `#print axioms` per headline declaration. |
| [tools/](lean/tools/) | `verify_catalogue.py`, the sequential, memory-capped verifier for the catalogue, with its own [README](lean/tools/README.md). |

The development has about 4,100 modules. Most of them are generated certificate data; the hand-written mathematics is in `Foundation/`, `Paper/`, `Fisher/` and the smaller `Methods/` libraries.

## The classification

Each row module [lean/Taeyoung/Examples/GraphNNN.lean](lean/Taeyoung/Examples/) has the same shape:

* `graph : SimpleGraph (Fin n)`, the graph as an explicit edge list;
* `metadata : CatalogueRow`, its Atlas number, vertex and edge counts, chromatic number, graph6 string and status;
* `status : SatisfiesLowerBound graph` for a positive row, or `status : ViolatesLowerBound graph` for a negative one.

A positive row applies one of the general theorems, an estimate specific to the graph, or an exact certificate, transported to the row's graph along an explicit isomorphism that is checked by computation. A negative row exhibits a finite step graphon with rational masses and values; its homomorphism density is a single kernel-evaluated sum of natural numbers, and the chromatic polynomial comes from kernel-evaluated colouring counts. The statuses agree with Theorem 1.7 and Figure 2 of the paper.

The table lists every row. Graphs are identified by their numbers in Read and Wilson's *An Atlas of Graphs* (the numbering of NetworkX's `graph_atlas`) and by their graph6 strings. The last column names the method and links to the row's module, whose header explains the proof.

| Atlas | $v$ | $e$ | $\chi$ | graph6 | Status | Proof checked by Lean |
|---:|---:|---:|---:|:---:|:---:|:---|
| 7 | 3 | 3 | 3 | <code>Bw</code> | 🟢 **Positive** | [Pure-chordal theorem](lean/Taeyoung/Examples/Graph007.lean): $K_3$ is a single clique bag |
| 15 | 4 | 4 | 3 | <code>CN</code> | 🟢 **Positive** | [Rooted triangle-tree theorem](lean/Taeyoung/Examples/Graph015.lean): the paw, a triangle with one pendant leaf; conditioning on the root, the weighted rooted-triangle inequality and Jensen |
| 17 | 4 | 5 | 3 | <code>C&#124;</code> | 🟢 **Positive** | [Pure-chordal theorem](lean/Taeyoung/Examples/Graph017.lean): a clique tree with 2 bags, every maximal clique of size 3 |
| 18 | 4 | 6 | 4 | <code>C~</code> | 🟢 **Positive** | [Pure-chordal theorem](lean/Taeyoung/Examples/Graph018.lean): $K_4$ is a single clique bag |
| 34 | 5 | 5 | 3 | <code>D@{</code> | 🟢 **Positive** | [Rooted triangle-tree theorem](lean/Taeyoung/Examples/Graph034.lean): all pendant leaves share one triangle root; conditioning on the root, the weighted rooted-triangle inequality and Jensen |
| 35 | 5 | 5 | 3 | <code>Dx_</code> | 🟢 **Positive** | [Two-root book-leaf theorem](lean/Taeyoung/Examples/Graph035.lean): pendant leaves at both ends of the book spine; the page bound $H_0\ge d(x)+d(y)-1$, AM–GM, and the edge geometric-mean estimate $\iint W\sqrt{d(x)d(y)}\ge p^2$ |
| 36 | 5 | 5 | 3 | <code>DJc</code> | 🟢 **Positive** | [Rooted triangle-tree theorem](lean/Taeyoung/Examples/Graph036.lean): a triangle with one two-edge tail; conditioning on the root gives $\int\tau A$, then the pointwise Goodman bound $\tau\ge 2A-p$ and Jensen for $A$ |
| 38 | 5 | 5 | 3 | <code>Dhc</code> | 🟢 **Positive** | [Odd-cycle theorem](lean/Taeyoung/Examples/Graph038.lean): the analytic $C_5$ inequality |
| 40 | 5 | 6 | 3 | <code>DjW</code> | 🟢 **Positive** | [Forest-cone theorem](lean/Taeyoung/Examples/Graph040.lean): cone over a forest of stars and edges; Jensen bounds the forest, then the affine-product tangent at $2-1/p$ and the weighted rooted-triangle inequality bound the cone |
| 41 | 5 | 6 | 3 | <code>Db[</code> | 🟢 **Positive** | [Page-rooted book-leaf theorem](lean/Taeyoung/Examples/Graph041.lean): a two-page book with one leaf on a page; Cauchy–Schwarz in the page variable and on the spine reduces it to $\int d^{1/2}\tau$, then the weighted rooted-triangle inequality and Jensen |
| 42 | 5 | 6 | 3 | <code>D&#96;{</code> | 🟢 **Positive** | [Pure-chordal theorem](lean/Taeyoung/Examples/Graph042.lean): a clique tree with 2 bags, every maximal clique of size 3 |
| 43 | 5 | 6 | 3 | <code>Dlc</code> | 🟢 **Positive** | [Exact rooted interval-SOS certificate](lean/Taeyoung/Examples/Graph043.lean): on the full interval $[1/2,1]$, checked by a chain of 1,097 `decide +kernel` modules |
| 45 | 5 | 7 | 4 | <code>DJ{</code> | 🟢 **Positive** | [Clique common-leaf theorem](lean/Taeyoung/Examples/Graph045.lean): $K_4$ with all pendant leaves at one clique vertex; conditioning on that vertex, the tangent of the clique polynomial at $2-1/p$ and the weighted rooted-triangle inequality |
| 46 | 5 | 7 | 3 | <code>DF{</code> | 🟢 **Positive** | [Pure-chordal theorem](lean/Taeyoung/Examples/Graph046.lean): a clique tree with 3 bags, every maximal clique of size 3 |
| 47 | 5 | 7 | 3 | <code>Djs</code> | 🟢 **Positive** | [Pure-chordal theorem](lean/Taeyoung/Examples/Graph047.lean): a clique tree with 3 bags, every maximal clique of size 3 |
| 48 | 5 | 7 | 3 | <code>D]w</code> | 🔴 **Negative** | [Counterexample](lean/Taeyoung/Examples/Graph048.lean) four-part graphon, $p=2/3$: $t\approx 0.049382<4/81=\Phi_H(p)$ |
| 49 | 5 | 8 | 4 | <code>Df{</code> | 🟢 **Positive** | [Special-cone theorem](lean/Taeyoung/Examples/Graph049.lean): the cone over the paw; the cubic tangent at $2-1/p$ and the weighted rooted-triangle inequality |
| 50 | 5 | 8 | 3 | <code>Dl{</code> | 🔴 **Negative** | [Counterexample](lean/Taeyoung/Examples/Graph050.lean) four-part graphon, $p=2/3$: $t\approx 0.0246913<2/81=\Phi_H(p)$ |
| 51 | 5 | 9 | 4 | <code>Dn{</code> | 🟢 **Positive** | [Pure-chordal theorem](lean/Taeyoung/Examples/Graph051.lean): a clique tree with 2 bags, every maximal clique of size 4 |
| 52 | 5 | 10 | 5 | <code>D~{</code> | 🟢 **Positive** | [Pure-chordal theorem](lean/Taeyoung/Examples/Graph052.lean): $K_5$ is a single clique bag |
| 84 | 6 | 5 | 3 | <code>ECd_</code> | 🟢 **Positive** | [Component multiplicativity](lean/Taeyoung/Examples/Graph084.lean): $K_3$ by the pure-chordal clique bound and $P_3$ by $t(P_3,W)\ge p^2$ |
| 92 | 6 | 6 | 3 | <code>E?Fw</code> | 🟢 **Positive** | [Rooted triangle-tree theorem](lean/Taeyoung/Examples/Graph092.lean): all pendant leaves share one triangle root; conditioning on the root, the weighted rooted-triangle inequality and Jensen |
| 93 | 6 | 6 | 3 | <code>EC{O</code> | 🟢 **Positive** | [Two-root book-leaf theorem](lean/Taeyoung/Examples/Graph093.lean): pendant leaves at both ends of the book spine; the page bound $H_0\ge d(x)+d(y)-1$, AM–GM, and the edge geometric-mean estimate $\iint W\sqrt{d(x)d(y)}\ge p^2$ |
| 94 | 6 | 6 | 3 | <code>E@dW</code> | 🟢 **Positive** | [Whiskering of $K_3$](lean/Taeyoung/Examples/Graph094.lean): a degree-biased change of measure, path Sidorenko $t(P_4,W)\ge p^3$, and Goodman |
| 95 | 6 | 6 | 3 | <code>EG}?</code> | 🟢 **Positive** | [Mixed rooted-triangle branch theorem](lean/Taeyoung/Examples/Graph095.lean): pointwise Goodman $\tau\ge 2A-p$, weighted Cauchy–Schwarz and path Sidorenko |
| 97 | 6 | 6 | 3 | <code>EYWO</code> | 🟢 **Positive** | [Adjacent-root leaf and two-edge-tail theorem](lean/Taeyoung/Examples/Graph097.lean): a two-edge inclusion–exclusion and Cauchy–Schwarz reduce to $(d(x),A(x))$, closed by an exact supporting plane |
| 100 | 6 | 6 | 3 | <code>EsCW</code> | 🟢 **Positive** | [Triangle two-leaf-broom theorem](lean/Taeyoung/Examples/Graph100.lean): Cauchy–Schwarz and Goodman reduce to $(d(x),A(x))$, closed by an exact supporting plane |
| 102 | 6 | 6 | 3 | <code>EJe?</code> | 🟢 **Positive** | [Odd-walk theorem](lean/Taeyoung/Examples/Graph102.lean): pointwise Goodman against $T_W^3\mathbf 1$ and the graphon odd-walk inequality $t(P_5,W)^3\ge t(P_3,W)^5$ |
| 104 | 6 | 6 | 3 | <code>Ehd?</code> | 🟢 **Positive** | [Odd-cycle one-leaf theorem](lean/Taeyoung/Examples/Graph104.lean): rotation averaging and AM–GM move to a degree-biased measure, where the $C_5$ inequality applies; Jensen and Hölder close it |
| 106 | 6 | 6 | 3 | <code>EJaG</code> | 🟢 **Positive** | [Pure-chordal theorem](lean/Taeyoung/Examples/Graph106.lean): a clique tree with 2 bags, every maximal clique of size 3 |
| 111 | 6 | 7 | 3 | <code>EB{G</code> | 🟢 **Positive** | [Forest-cone theorem](lean/Taeyoung/Examples/Graph111.lean): cone over a forest of stars and edges; Jensen bounds the forest, then the affine-product tangent at $2-1/p$ and the weighted rooted-triangle inequality bound the cone |
| 112 | 6 | 7 | 3 | <code>EhX_</code> | 🟢 **Positive** | [Two-root book-leaf theorem](lean/Taeyoung/Examples/Graph112.lean): pendant leaves at both ends of the book spine; the page bound $H_0\ge d(x)+d(y)-1$, AM–GM, and the edge geometric-mean estimate $\iint W\sqrt{d(x)d(y)}\ge p^2$ |
| 113 | 6 | 7 | 3 | <code>E^_O</code> | 🟢 **Positive** | [Diamond orbit-balanced leaf theorem](lean/Taeyoung/Examples/Graph113.lean): an orbit swap and AM–GM move to the $\sqrt d$-biased measure, where the diamond bound applies |
| 114 | 6 | 7 | 3 | <code>EJwG</code> | 🟢 **Positive** | [Page-rooted book-leaf theorem](lean/Taeyoung/Examples/Graph114.lean): a two-page book with two leaves on one page; Cauchy–Schwarz in the page variable and on the spine reduces it to $\int d\,\tau$, then the weighted rooted-triangle inequality and Jensen |
| 115 | 6 | 7 | 3 | <code>E&#96;Xg</code> | 🟢 **Positive** | [Edge self-amalgam of the paw](lean/Taeyoung/Examples/Graph115.lean): Cauchy–Schwarz gives $t\ge t(\mathrm{paw},W)^2/p$, and the paw bound is $p^2(2p-1)$ |
| 117 | 6 | 7 | 3 | <code>EtaG</code> | 🟢 **Positive** | [Forest-cone theorem](lean/Taeyoung/Examples/Graph117.lean): cone over a forest of stars and edges; Jensen bounds the forest, then the affine-product tangent at $2-1/p$ and the weighted rooted-triangle inequality bound the cone |
| 118 | 6 | 7 | 3 | <code>Eht?</code> | 🟢 **Positive** | [Compact four-root interval SOS](lean/Taeyoung/Examples/Graph118.lean): exact integer Gram matrices and the interval identity, checked in the kernel |
| 119 | 6 | 7 | 3 | <code>EtoO</code> | 🟢 **Positive** | [Bowtie outer-leaf theorem](lean/Taeyoung/Examples/Graph119.lean): orbit averaging, AM–GM and Cauchy–Schwarz move to the $d^{1/6}$-biased measure, where Goodman applies |
| 120 | 6 | 7 | 3 | <code>EB}?</code> | 🟢 **Positive** | [Triangle-book two-edge-tail theorem](lean/Taeyoung/Examples/Graph120.lean): weighted Cauchy–Schwarz and two lower bounds from the pointwise Goodman estimate $\tau\ge 2A-p$ |
| 122 | 6 | 7 | 3 | <code>Eld?</code> | 🟢 **Positive** | [Compact four-root interval SOS](lean/Taeyoung/Examples/Graph122.lean): exact integer Gram matrices and the interval identity, checked in the kernel |
| 123 | 6 | 7 | 3 | <code>EJy?</code> | 🟢 **Positive** | [Page-rooted two-edge-tail theorem](lean/Taeyoung/Examples/Graph123.lean): two Cauchy–Schwarz steps reduce to $\int\sqrt{A}\,\tau\ge p^2(2p-1)$, an affine minorant |
| 124 | 6 | 7 | 3 | <code>Exd?</code> | 🟢 **Positive** | [Compact four-root interval SOS](lean/Taeyoung/Examples/Graph124.lean): exact integer Gram matrices and the interval identity, checked in the kernel |
| 126 | 6 | 7 | 3 | <code>ERUO</code> | 🟢 **Positive** | [Atlas 126 supporting-plane theorem](lean/Taeyoung/Examples/Graph126.lean): a triangle and a $C_4$ sharing a vertex; supporting planes covering the whole domain, with exact Bernstein certificates |
| 127 | 6 | 7 | 3 | <code>EZEG</code> | 🟢 **Positive** | [Compact four-root interval SOS](lean/Taeyoung/Examples/Graph127.lean): exact integer Gram matrices and the interval identity, checked in the kernel |
| 129 | 6 | 7 | 3 | <code>EheO</code> | 🔴 **Negative** | [Counterexample](lean/Taeyoung/Examples/Graph129.lean) constant graphon $W\equiv3/4$, $p=3/4$: $t=2187/16384<69/512=\Phi_H(p)$ |
| 130 | 6 | 7 | 3 | <code>E{CW</code> | 🟢 **Positive** | [Induced and four-root interval SOS](lean/Taeyoung/Examples/Graph130.lean): exact integer Gram matrices and the interval identity, checked in the kernel |
| 133 | 6 | 8 | 4 | <code>E~a?</code> | 🟢 **Positive** | [Clique common-leaf theorem](lean/Taeyoung/Examples/Graph133.lean): $K_4$ with all pendant leaves at one clique vertex; conditioning on that vertex, the tangent of the clique polynomial at $2-1/p$ and the weighted rooted-triangle inequality |
| 134 | 6 | 8 | 4 | <code>E~_O</code> | 🟢 **Positive** | [Clique distributed-leaf theorem](lean/Taeyoung/Examples/Graph134.lean): one exchange and AM–GM move to the $\sqrt d$-biased measure, where the $K_4$ bound applies |
| 135 | 6 | 8 | 3 | <code>EzW_</code> | 🟢 **Positive** | [Forest-cone theorem](lean/Taeyoung/Examples/Graph135.lean): cone over a forest of stars and edges; Jensen bounds the forest, then the affine-product tangent at $2-1/p$ and the weighted rooted-triangle inequality bound the cone |
| 136 | 6 | 8 | 3 | <code>Ejt?</code> | 🟢 **Positive** | [Forest-cone theorem](lean/Taeyoung/Examples/Graph136.lean): cone over $P_4\sqcup K_1$; path Sidorenko $t(P_4,W)\ge p^3$ bounds the forest, then the affine-product tangent at $2-1/p$ and the weighted rooted-triangle inequality bound the cone |
| 137 | 6 | 8 | 3 | <code>EjsG</code> | 🟢 **Positive** | [Page-paw branch theorem](lean/Taeyoung/Examples/Graph137.lean): Cauchy–Schwarz in the page variable, edge Cauchy–Schwarz and Jensen reduce to $\int d^{1/3}\tau\ge p^{4/3}(2p-1)$ |
| 138 | 6 | 8 | 3 | <code>Ez&#96;_</code> | 🟢 **Positive** | [Page-rooted book-leaf theorem](lean/Taeyoung/Examples/Graph138.lean): a three-page book with one leaf on a page; two staggered Cauchy–Schwarz compressions reduce it to $\int d^{1/3}\tau$, then the weighted rooted-triangle inequality and Jensen |
| 139 | 6 | 8 | 3 | <code>Eju?</code> | 🟢 **Positive** | [Page-paw branch theorem](lean/Taeyoung/Examples/Graph139.lean): Cauchy–Schwarz in the page variable, edge Cauchy–Schwarz and Jensen reduce to $\int d^{1/3}\tau\ge p^{4/3}(2p-1)$ |
| 140 | 6 | 8 | 3 | <code>Ev&#96;_</code> | 🔴 **Negative** | [Counterexample](lean/Taeyoung/Examples/Graph140.lean) four-part graphon, $p=2/3$: $t\approx 0.032921<8/243=\Phi_H(p)$ |
| 141 | 6 | 8 | 3 | <code>EXSw</code> | 🔴 **Negative** | [Counterexample](lean/Taeyoung/Examples/Graph141.lean) four-part graphon, $p=2/3$: $t\approx 0.0329217<8/243=\Phi_H(p)$ |
| 142 | 6 | 8 | 4 | <code>E~AG</code> | 🟢 **Positive** | [$K_4$ two-edge-tail theorem](lean/Taeyoung/Examples/Graph142.lean): Goodman in the rooted link and an exact supporting plane in $(d,A)$ |
| 143 | 6 | 8 | 3 | <code>Er&#96;o</code> | 🔴 **Negative** | [Counterexample](lean/Taeyoung/Examples/Graph143.lean) four-part graphon, $p=2/3$: $t\approx 0.0329217<8/243=\Phi_H(p)$ |
| 144 | 6 | 8 | 3 | <code>EB}G</code> | 🟢 **Positive** | [Pure-chordal theorem](lean/Taeyoung/Examples/Graph144.lean): a clique tree with 3 bags, every maximal clique of size 3 |
| 145 | 6 | 8 | 3 | <code>Exe_</code> | 🟢 **Positive** | [Page-concentration theorem](lean/Taeyoung/Examples/Graph145.lean): the pointwise Cauchy–Schwarz $Q^2\le PR$ gives $t(H_{145},W)\ge t(H_{148},W)$, then Atlas 148 |
| 147 | 6 | 8 | 3 | <code>EhMg</code> | 🟢 **Positive** | [Compact four-root interval SOS](lean/Taeyoung/Examples/Graph147.lean): exact integer Gram matrices and the interval identity, checked in the kernel |
| 148 | 6 | 8 | 3 | <code>EyUG</code> | 🟢 **Positive** | [Paw-bias projection theorem](lean/Taeyoung/Examples/Graph148.lean): for $p\ge3/5$, a two-term Bessel projection and a Bernstein-certified supporting line; for $p\le3/5$, the sharp paw bias with Fisher's triangle theorem |
| 149 | 6 | 8 | 3 | <code>Ele_</code> | 🔴 **Negative** | [Tensor counterexample](lean/Taeyoung/Examples/Graph149.lean) $T_{5} \otimes T_{6}$, $p=2/3$: $t=3827/101250<10/243=\Phi_H(p)$ |
| 150 | 6 | 8 | 3 | <code>EJyG</code> | 🟢 **Positive** | [Pure-chordal theorem](lean/Taeyoung/Examples/Graph150.lean): a clique tree with 3 bags, every maximal clique of size 3 |
| 151 | 6 | 8 | 3 | <code>EhdW</code> | 🟢 **Positive** | [Compact four-root interval SOS](lean/Taeyoung/Examples/Graph151.lean): exact integer Gram matrices and the interval identity, checked in the kernel |
| 152 | 6 | 8 | 3 | <code>EhNG</code> | 🔴 **Negative** | [Counterexample](lean/Taeyoung/Examples/Graph152.lean) five-part graphon $W_\varepsilon$, $\varepsilon=1/3000$, $p=18750093281/37500000000$: $t\approx 3.086\times10^{-12}<3.094\times10^{-12}\approx\Phi_H(p)$ |
| 153 | 6 | 8 | 3 | <code>Ehf_</code> | 🟢 **Positive** | [Compact four-root interval SOS](lean/Taeyoung/Examples/Graph153.lean): exact integer Gram matrices and the interval identity, checked in the kernel |
| 156 | 6 | 9 | 4 | <code>E~H_</code> | 🟢 **Positive** | [Special-cone theorem](lean/Taeyoung/Examples/Graph156.lean): the cone over the paw and an isolated vertex; the cubic tangent at $2-1/p$ and the weighted rooted-triangle inequality |
| 157 | 6 | 9 | 4 | <code>E~&#96;_</code> | 🟢 **Positive** | [Compact four-root interval SOS](lean/Taeyoung/Examples/Graph157.lean): exact integer Gram matrices and the interval identity, checked in the kernel |
| 158 | 6 | 9 | 3 | <code>El{G</code> | 🔴 **Negative** | [Counterexample](lean/Taeyoung/Examples/Graph158.lean) four-part graphon, $p=2/3$: $t\approx 0.0164608<4/243=\Phi_H(p)$ |
| 159 | 6 | 9 | 3 | <code>EZSw</code> | 🔴 **Negative** | [Counterexample](lean/Taeyoung/Examples/Graph159.lean) three-part graphon, $p=2/3$: $t\approx 0.016459<4/243=\Phi_H(p)$ |
| 160 | 6 | 9 | 4 | <code>E~@g</code> | 🟢 **Positive** | [Weighted-$K_4$ supporting-plane theorem](lean/Taeyoung/Examples/Graph160.lean): the page reduction $t\ge 2\,t(K_4\text{ two-edge tail})-p\,t(K_4)$, Goodman in the rooted link, and an exact supporting plane |
| 161 | 6 | 9 | 3 | <code>E?~w</code> | 🟢 **Positive** | [Pure-chordal theorem](lean/Taeyoung/Examples/Graph161.lean): a clique tree with 4 bags, every maximal clique of size 3 |
| 162 | 6 | 9 | 3 | <code>E&#124;e_</code> | 🟢 **Positive** | [Pure-chordal theorem](lean/Taeyoung/Examples/Graph162.lean): a clique tree with 4 bags, every maximal clique of size 3 |
| 163 | 6 | 9 | 3 | <code>EyuG</code> | 🟢 **Positive** | [Pure-chordal theorem](lean/Taeyoung/Examples/Graph163.lean): a clique tree with 4 bags, every maximal clique of size 3 |
| 164 | 6 | 9 | 3 | <code>EyVG</code> | 🟢 **Positive** | [Pure-chordal theorem](lean/Taeyoung/Examples/Graph164.lean): a clique tree with 4 bags, every maximal clique of size 3 |
| 165 | 6 | 9 | 4 | <code>E~aG</code> | 🟢 **Positive** | [Special-cone theorem](lean/Taeyoung/Examples/Graph165.lean): the cone over $K_3\sqcup K_2$; the cubic tangent at $2-1/p$ and the weighted rooted-triangle inequality |
| 166 | 6 | 9 | 3 | <code>ElfO</code> | 🔴 **Negative** | [Counterexample](lean/Taeyoung/Examples/Graph166.lean) four-part graphon, $p=9/16$: $t=465/262144<477/262144=\Phi_H(p)$ |
| 167 | 6 | 9 | 3 | <code>E^eG</code> | 🟢 **Positive** | [Pure-chordal theorem](lean/Taeyoung/Examples/Graph167.lean): a clique tree with 4 bags, every maximal clique of size 3 |
| 168 | 6 | 9 | 3 | <code>E^MG</code> | 🟢 **Positive** | [Compact four-root interval SOS](lean/Taeyoung/Examples/Graph168.lean): exact integer Gram matrices and the interval identity, checked in the kernel |
| 169 | 6 | 9 | 4 | <code>Exf_</code> | 🟢 **Positive** | [Compact four-root interval SOS](lean/Taeyoung/Examples/Graph169.lean): exact integer Gram matrices and the interval identity, checked in the kernel |
| 170 | 6 | 9 | 3 | <code>EO~o</code> | 🔴 **Negative** | [Tensor counterexample](lean/Taeyoung/Examples/Graph170.lean) $T_{5} \otimes T_{6}$, $p=2/3$: $t=1241/50625<8/243=\Phi_H(p)$ |
| 171 | 6 | 9 | 3 | <code>Ehew</code> | 🟢 **Positive** | [Compact four-root interval SOS](lean/Taeyoung/Examples/Graph171.lean): exact integer Gram matrices and the interval identity, checked in the kernel |
| 172 | 6 | 9 | 3 | <code>Elf_</code> | 🔴 **Negative** | [Counterexample](lean/Taeyoung/Examples/Graph172.lean) four-part graphon, $p=9/16$: $t=3/2048<477/262144=\Phi_H(p)$ |
| 173 | 6 | 9 | 3 | <code>ElMg</code> | 🔴 **Negative** | [Tensor counterexample](lean/Taeyoung/Examples/Graph173.lean) $T_{5} \otimes T_{6}$, $p=2/3$: $t=44/1875<2/81=\Phi_H(p)$ |
| 174 | 6 | 9 | 3 | <code>EtTg</code> | 🟢 **Positive** | [Compact four-root interval SOS](lean/Taeyoung/Examples/Graph174.lean): exact integer Gram matrices and the interval identity, checked in the kernel |
| 177 | 6 | 10 | 4 | <code>En{G</code> | 🟢 **Positive** | [Base-cone theorem](lean/Taeyoung/Examples/Graph177.lean): the cone over Atlas 33; its verified bound, the tangent at $2-1/p$ and the weighted rooted-triangle inequality give the cone's target |
| 178 | 6 | 10 | 4 | <code>En}?</code> | 🟢 **Positive** | [Half-degree weighted-$K_4$ theorem](lean/Taeyoung/Examples/Graph178.lean): two Cauchy–Schwarz steps and two exact supporting planes in $(d,A,\tau)$ |
| 179 | 6 | 10 | 4 | <code>E_~w</code> | 🟢 **Positive** | [Base-cone theorem](lean/Taeyoung/Examples/Graph179.lean): the cone over Atlas 34; its verified bound, the tangent at $2-1/p$ and the weighted rooted-triangle inequality give the cone's target |
| 180 | 6 | 10 | 4 | <code>EjtW</code> | 🟢 **Positive** | [Two-root book-leaf theorem](lean/Taeyoung/Examples/Graph180.lean): the cone over Atlas 35 |
| 181 | 6 | 10 | 4 | <code>E^mG</code> | 🟢 **Positive** | [Compact four-root interval SOS](lean/Taeyoung/Examples/Graph181.lean): exact integer Gram matrices and the interval identity, checked in the kernel |
| 182 | 6 | 10 | 3 | <code>E^Mg</code> | 🔴 **Negative** | [Tensor counterexample](lean/Taeyoung/Examples/Graph182.lean) $T_{4} \otimes T_{4}$, $p=9/16$: $t=81/65536<351/262144=\Phi_H(p)$ |
| 183 | 6 | 10 | 4 | <code>EjvG</code> | 🟢 **Positive** | [Base-cone theorem](lean/Taeyoung/Examples/Graph183.lean): the cone over Atlas 36; its verified bound, the tangent at $2-1/p$ and the weighted rooted-triangle inequality give the cone's target |
| 184 | 6 | 10 | 3 | <code>Elfo</code> | 🔴 **Negative** | [Tensor counterexample](lean/Taeyoung/Examples/Graph184.lean) $T_{4} \otimes T_{4}$, $p=9/16$: $t=81/65536<351/262144=\Phi_H(p)$ |
| 185 | 6 | 10 | 4 | <code>Exv_</code> | 🟢 **Positive** | [Compact four-root interval SOS](lean/Taeyoung/Examples/Graph185.lean): exact integer Gram matrices and the interval identity, checked in the kernel |
| 186 | 6 | 10 | 3 | <code>ErXw</code> | 🔴 **Negative** | [Tensor counterexample](lean/Taeyoung/Examples/Graph186.lean) $T_{5} \otimes T_{6}$, $p=2/3$: $t=224/16875<4/243=\Phi_H(p)$ |
| 187 | 6 | 10 | 4 | <code>Ehfw</code> | 🟢 **Positive** | [Odd-cycle cone theorem](lean/Taeyoung/Examples/Graph187.lean): the cone over $C_5$; the analytic $C_5$ inequality and the tangent at $2-1/p$ |
| 188 | 6 | 10 | 3 | <code>EzNG</code> | 🟢 **Positive** | [Compact four-root interval SOS](lean/Taeyoung/Examples/Graph188.lean): exact integer Gram matrices and the interval identity, checked in the kernel |
| 189 | 6 | 10 | 3 | <code>E^NG</code> | 🔴 **Negative** | [Tensor counterexample](lean/Taeyoung/Examples/Graph189.lean) $T_{5} \otimes T_{6}$, $p=2/3$: $t=767/50625<4/243=\Phi_H(p)$ |
| 190 | 6 | 10 | 3 | <code>EyUw</code> | 🔴 **Negative** | [Tensor counterexample](lean/Taeyoung/Examples/Graph190.lean) $T_{5} \otimes T_{6}$, $p=2/3$: $t=224/16875<4/243=\Phi_H(p)$ |
| 191 | 6 | 11 | 5 | <code>E~&#124;?</code> | 🟢 **Positive** | [Clique common-leaf theorem](lean/Taeyoung/Examples/Graph191.lean): $K_5$ with all pendant leaves at one clique vertex; conditioning on that vertex, the tangent of the clique polynomial at $2-1/p$ and the weighted rooted-triangle inequality |
| 192 | 6 | 11 | 4 | <code>E~Xo</code> | 🟢 **Positive** | [Base-cone theorem](lean/Taeyoung/Examples/Graph192.lean): the cone over Atlas 40; its verified bound, the tangent at $2-1/p$ and the weighted rooted-triangle inequality give the cone's target |
| 193 | 6 | 11 | 4 | <code>En}G</code> | 🟢 **Positive** | [Page-rooted book-leaf theorem](lean/Taeyoung/Examples/Graph193.lean): the cone over Atlas 41 |
| 194 | 6 | 11 | 4 | <code>E~wW</code> | 🟢 **Positive** | [Compact four-root interval SOS](lean/Taeyoung/Examples/Graph194.lean): exact integer Gram matrices and the interval identity, checked in the kernel |
| 195 | 6 | 11 | 4 | <code>EyVw</code> | 🟢 **Positive** | [Pure-chordal theorem](lean/Taeyoung/Examples/Graph195.lean): a clique tree with 2 bags, every maximal clique of size 4 |
| 196 | 6 | 11 | 4 | <code>ER~g</code> | 🟢 **Positive** | [House-cone lift of Atlas 43](lean/Taeyoung/Examples/Graph196.lean): the normalized-link cone argument applied to the Atlas 43 theorem |
| 197 | 6 | 11 | 3 | <code>E}^G</code> | 🔴 **Negative** | [Tensor counterexample](lean/Taeyoung/Examples/Graph197.lean) $T_{5} \otimes T_{6}$, $p=2/3$: $t=731/101250<2/243=\Phi_H(p)$ |
| 198 | 6 | 11 | 3 | <code>Ep~o</code> | 🔴 **Negative** | [Tensor counterexample](lean/Taeyoung/Examples/Graph198.lean) $T_{5} \otimes T_{6}$, $p=2/3$: $t=731/101250<2/243=\Phi_H(p)$ |
| 199 | 6 | 11 | 4 | <code>El^g</code> | 🟢 **Positive** | [Compact four-root interval SOS](lean/Taeyoung/Examples/Graph199.lean): exact integer Gram matrices and the interval identity, checked in the kernel |
| 200 | 6 | 12 | 5 | <code>E~{W</code> | 🟢 **Positive** | [Base-cone theorem](lean/Taeyoung/Examples/Graph200.lean): the cone over Atlas 45; its verified bound, the tangent at $2-1/p$ and the weighted rooted-triangle inequality give the cone's target |
| 201 | 6 | 12 | 4 | <code>E~z_</code> | 🟢 **Positive** | [Pure-chordal theorem](lean/Taeyoung/Examples/Graph201.lean): a clique tree with 3 bags, every maximal clique of size 4 |
| 202 | 6 | 12 | 4 | <code>Ep~w</code> | 🟢 **Positive** | [Pure-chordal theorem](lean/Taeyoung/Examples/Graph202.lean): a clique tree with 3 bags, every maximal clique of size 4 |
| 203 | 6 | 12 | 4 | <code>E~^G</code> | 🟢 **Positive** | [Induced and four-root interval SOS](lean/Taeyoung/Examples/Graph203.lean): exact integer Gram matrices and the interval identity, checked in the kernel |
| 204 | 6 | 12 | 3 | <code>EznW</code> | 🔴 **Negative** | [Tensor counterexample](lean/Taeyoung/Examples/Graph204.lean) $T_{5} \otimes T_{6}$, $p=2/3$: $t=221/50625<2/243=\Phi_H(p)$ |
| 205 | 6 | 13 | 5 | <code>E~~G</code> | 🟢 **Positive** | [Base-cone theorem](lean/Taeyoung/Examples/Graph205.lean): the cone over Atlas 49; its verified bound, the tangent at $2-1/p$ and the weighted rooted-triangle inequality give the cone's target |
| 206 | 6 | 13 | 4 | <code>E~nW</code> | 🔴 **Negative** | [Counterexample](lean/Taeyoung/Examples/Graph206.lean) three-part graphon, $p=25/36$: $t=77731841/48922361856<16975/10077696=\Phi_H(p)$ |
| 207 | 6 | 14 | 5 | <code>Ez~w</code> | 🟢 **Positive** | [Pure-chordal theorem](lean/Taeyoung/Examples/Graph207.lean): a clique tree with 2 bags, every maximal clique of size 5 |
| 208 | 6 | 15 | 6 | <code>E~~w</code> | 🟢 **Positive** | [Pure-chordal theorem](lean/Taeyoung/Examples/Graph208.lean): $K_6$ is a single clique bag |

## Notes

The paper proves the general theorems and constructs the counterexamples. For 70 of the 94 positive graphs the proof is an argument specific to that graph: 51 of them are written up in the notes in [notes/](notes/), and the 19 graphs proved by compact four-root certificates have certificate records there. These are the working notes behind the formalization. They were drafted with AI assistance during the development and have not been polished or refereed. The Lean proof is the authoritative version, and where a note and the Lean proof take different routes, the module header says so.

| Note | Rows |
|---|---|
| [rooted_triangle_tree_extensions.pdf](notes/rooted_triangle_tree_extensions.pdf) | 15, 34, 36, 92 |
| [two_root_triangle_leaf_cones.pdf](notes/two_root_triangle_leaf_cones.pdf) | 35, 93, 112, 180 |
| [six_verified_base_cones.pdf](notes/six_verified_base_cones.pdf) | 40, 111, 117, 135, 136, 177, 179, 183, 192, 200, 205 |
| [forest_cone_graphon_bound.pdf](notes/forest_cone_graphon_bound.pdf) | 40, 111, 117, 135, 136, 192 |
| [page_rooted_triangle_book_leaves.pdf](notes/page_rooted_triangle_book_leaves.pdf) | 41, 114, 138, 193 |
| [atlas43_exact_rooted_sos.pdf](notes/atlas43_exact_rooted_sos.pdf) | 43, 196 |
| [clique_common_leaf_extensions.pdf](notes/clique_common_leaf_extensions.pdf) | 45, 133, 191 |
| [paw_triangle_edge_cones.pdf](notes/paw_triangle_edge_cones.pdf) | 49, 156, 165 |
| [whiskering.pdf](notes/whiskering.pdf) | 94 |
| [mixed_rooted_triangle_branches.pdf](notes/mixed_rooted_triangle_branches.pdf) | 95 |
| [triangle_adjacent_leaf_tail.pdf](notes/triangle_adjacent_leaf_tail.pdf) | 97 |
| [triangle_two_leaf_broom.pdf](notes/triangle_two_leaf_broom.pdf) | 100 |
| [blekherman_raymond.pdf](notes/blekherman_raymond.pdf) | 102 |
| [triangle_three_edge_tail.pdf](notes/triangle_three_edge_tail.pdf) | 102 |
| [odd_cycle_one_leaf.pdf](notes/odd_cycle_one_leaf.pdf) | 104 |
| [bowtie_outer_leaves.pdf](notes/bowtie_outer_leaves.pdf) | 104, 119 |
| [clique_distributed_leaves.pdf](notes/clique_distributed_leaves.pdf) | 113, 134 |
| [diamond_orbit_balanced_leaves.pdf](notes/diamond_orbit_balanced_leaves.pdf) | 113 |
| [self_amalgam.pdf](notes/self_amalgam.pdf) | 115 |
| [triangle_book_two_edge_tail.pdf](notes/triangle_book_two_edge_tail.pdf) | 120 |
| [triangle_book_page_two_edge_tail.pdf](notes/triangle_book_page_two_edge_tail.pdf) | 123 |
| [atlas126_triangle_c4_vertex_supporting_plane.pdf](notes/atlas126_triangle_c4_vertex_supporting_plane.pdf) | 126 |
| [triangle_book_page_paw_branch.pdf](notes/triangle_book_page_paw_branch.pdf) | 137, 139, 148 |
| [k4_two_edge_tail.pdf](notes/k4_two_edge_tail.pdf) | 142 |
| [c4_triangle_page_concentration.pdf](notes/c4_triangle_page_concentration.pdf) | 145 |
| [atlas148_paw_bias_hilbert_projection.pdf](notes/atlas148_paw_bias_hilbert_projection.pdf) | 148 |
| [atlas160_k4_paw_edge_supporting_plane.pdf](notes/atlas160_k4_paw_edge_supporting_plane.pdf) | 160 |
| [atlas178_half_degree_weighted_k4.pdf](notes/atlas178_half_degree_weighted_k4.pdf) | 178 |

Each certificate record states which sum-of-squares identity the Lean modules check for the row, how the exact integer witnesses were produced, and the build measurements at the time.

| Record | Row |
|---|---|
| [atlas118_compact_certificate.md](notes/atlas118_compact_certificate.md) | 118 |
| [atlas122_compact_certificate.md](notes/atlas122_compact_certificate.md) | 122 |
| [atlas124_compact_certificate.md](notes/atlas124_compact_certificate.md) | 124 |
| [atlas126_compact_verification.md](notes/atlas126_compact_verification.md) | 126 |
| [atlas127_compact_certificate.md](notes/atlas127_compact_certificate.md) | 127 |
| [atlas130_compact_certificate.md](notes/atlas130_compact_certificate.md) | 130 |
| [atlas147_compact_certificate.md](notes/atlas147_compact_certificate.md) | 147 |
| [atlas151_compact_certificate.md](notes/atlas151_compact_certificate.md) | 151 |
| [atlas153_compact_certificate.md](notes/atlas153_compact_certificate.md) | 153 |
| [atlas157_compact_certificate.md](notes/atlas157_compact_certificate.md) | 157 |
| [atlas168_compact_certificate.md](notes/atlas168_compact_certificate.md) | 168 |
| [atlas169_compact_certificate.md](notes/atlas169_compact_certificate.md) | 169 |
| [atlas171_compact_certificate.md](notes/atlas171_compact_certificate.md) | 171 |
| [atlas174_compact_certificate.md](notes/atlas174_compact_certificate.md) | 174 |
| [atlas181_compact_certificate.md](notes/atlas181_compact_certificate.md) | 181 |
| [atlas185_compact_certificate.md](notes/atlas185_compact_certificate.md) | 185 |
| [atlas188_compact_certificate.md](notes/atlas188_compact_certificate.md) | 188 |
| [atlas194_compact_certificate.md](notes/atlas194_compact_certificate.md) | 194 |
| [atlas199_compact_certificate.md](notes/atlas199_compact_certificate.md) | 199 |
| [atlas203_compact_certificate.md](notes/atlas203_compact_certificate.md) | 203 |

## Density ranges and Turán optimality for the violating graphs

For each of the 23 violating graphs, [lean/Taeyoung/Paper/Refinements/GraphNNN.lean](lean/Taeyoung/Paper/Refinements/) proves its row of Table 1 of the paper, in the vocabulary of [Paper/Basic.lean](lean/Taeyoung/Paper/Basic.lean):

* `lowerBoundRange : SatisfiesLowerBoundOn graph S`, the inequality for every graphon whose edge density lies in $S$;
* `turanOptimal k (hk : k₀ ≤ k) : TuranOptimal graph k`, meaning that $T_k$ minimises $t(H,W)$ among graphons of edge density $1-1/k$;
* `not_turanOptimal_three`, `_four`, `_five : ¬ TuranOptimal graph k`.

| Graphs | Lower bound range | Optimality of $T_k$ |
|---|---|---|
| 152, 166, 172, 182, 184 | $p=2/3$ or $p\ge3/4$ | optimal for every $k\ge\chi(H)=3$ |
| 206 | $p\ge3/4$ | optimal for every $k\ge\chi(H)=4$ |
| 48, 50, 140, 141, 143, 158, 159, 197, 198 | $p\ge3/4$ | not at $k=3$; optimal for $k\ge4$ |
| 186 | $p=3/4$ or $p\ge4/5$ | not at $k=3$; optimal for $k\ge4$ |
| 190 | $p\ge4/5$ | not at $k=3,4$; optimal for $k\ge5$ |
| 173 | $p\ge4/5$ | not at $k=3$; optimal for $k\ge5$ ($k=4$ open) |
| 149, 170 | $p\ge1-(72\cdot6^{12})^{-1}$ | not at $k=3,4,5$; optimal for $k\ge72\cdot6^{12}$ |
| 189, 204 | $p\ge1-(72\cdot6^{12})^{-1}$ | not at $k=3,4$; optimal for $k\ge72\cdot6^{12}$ |
| 129 | none | not at any $k\ge4$ (`not_turanOptimal_constant`, `not_turanOptimal_tensor`) |

The ranges $p\ge3/4$ and $p\ge4/5$ and the single densities $p=2/3$ and $p=3/4$ are rational six-point sum-of-squares certificates, checked in [Methods/RootedSOS/Refinement/](lean/Taeyoung/Methods/RootedSOS/Refinement/). The ranges $p\ge1-(72\cdot6^{12})^{-1}$ are the explicit threshold of Theorem 1.6, closed at the endpoint. Optimality of $T_k$ is the bound at $p=1-1/k$; non-optimality is one of the counterexamples of Section 5.2. The 94 positive graphs have $T_k$ optimal for every $k\ge\chi(H)$ by `Taeyoung.Paper.turanOptimal_of_satisfiesLowerBound`. For graph 173 at $k=4$, only the upper bound $t(H_{173},T_4)=9/128$ of equation (5.1) is formalized (`Graph173.turan4_value`).

## Checking the development

### Requirements

* Lean 4, installed with [elan](https://github.com/leanprover/elan). The toolchain `leanprover/lean4:v4.31.0` is pinned in [lean/lean-toolchain](lean/lean-toolchain).
* Mathlib at tag `v4.31.0` (commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`) and `OddCycleBound` at commit `dbaea5a4d2c044a202f1e40647f4b24a1c77b313`, both pinned with their dependencies in [lean/lake-manifest.json](lean/lake-manifest.json).
* For the catalogue verifier: Python 3.11 or later with `psutil` and `networkx`.
* Memory: the general theorems and the refinements need a few GiB per Lean process. Several catalogue modules need 13–17 GiB each, so the full catalogue needs a machine with at least 32 GiB of RAM; see below.

### Setup

From [lean/](lean/), fetch the pinned packages together with Mathlib's prebuilt files, then compile `OddCycleBound` (about 10–20 minutes; each Lean process needs about 8 GiB, so keep the thread count low on a 16 GiB machine):

```sh
cd lean
lake exe cache get
LEAN_NUM_THREADS=3 lake build OddCycleBound OddCycleBound.Main
```

All commands below are run from `lean/`.

> [!WARNING]
> Do not run a plain `lake build` to verify the catalogue. The default target imports all 117 rows, Lake compiles modules in parallel with one worker per core, and several certificate modules need 13–17 GiB each, so a parallel build runs out of memory. Use the targets and the script below.

### The general theorems

```sh
LEAN_NUM_THREADS=3 lake build Taeyoung.CheckPaper
```

This compiles the `Paper` library and prints one line per headline declaration listed in [CheckPaper.lean](lean/Taeyoung/CheckPaper.lean). Every line must read

```
… depends on axioms: [propext, Classical.choice, Quot.sound]
```

### The density ranges and Turán optimality

```sh
LEAN_NUM_THREADS=3 lake build Taeyoung.CheckRefinements
```

This compiles the 24 refinement certificate chains (19 modules each, about 9 minutes of compile time per chain, so about 2.5 hours with three threads) and prints the axioms of every theorem in [CheckRefinements.lean](lean/Taeyoung/CheckRefinements.lean), with the same expected output.

### The catalogue

[lean/tools/verify_catalogue.py](lean/tools/verify_catalogue.py) verifies Theorem 1.7. It compiles every project module from source into a fresh build directory, one Lean process at a time with one thread under a memory cap (32 GiB by default), and after each row compiles a generated audit file that checks, inside Lean, that `GraphNNN.status` has exactly the statement `SatisfiesLowerBound graph` or `ViolatesLowerBound graph` matching the row's metadata, and that it depends on no axioms beyond `propext`, `Classical.choice` and `Quot.sound`. A `sorry` or a `native_decide` anywhere in the proof therefore fails the row. Before compiling, it checks with NetworkX that the 117 rows are exactly the Atlas graphs in scope, that each edge list is isomorphic to its Atlas graph with the stated invariants, and that the statuses agree with the table in this file. After the first verified row it runs two negative controls, an audit against the opposite statement and a proof by `sorry`, both of which must be rejected. After the rows it compiles `Taeyoung.Catalogue.Counts`.

```sh
python tools/verify_catalogue.py --plan            # list what will be compiled; compiles nothing
python tools/verify_catalogue.py                   # all 117 rows, then the kernel-checked counts
python tools/verify_catalogue.py --rows 17,43,127  # selected rows only
python tools/verify_catalogue.py --resume verification_runs/full-<timestamp>
```

The run directory `verification_runs/full-<timestamp>/` receives `REPORT.md`, the measurements of every module and unit, the compiler logs and the audit files. [lean/tools/README.md](lean/tools/README.md) describes every check, option and output.

Costs measured on the authors' machine (Windows 11, 20 logical CPUs of which one is used, 64 GiB of RAM, Mathlib prebuilt); [lean/VERIFICATION_SUMMARY.md](lean/VERIFICATION_SUMMARY.md) has the figure for every row, measured on the released sources:

| Verification | Time | Peak memory |
|---|---:|---:|
| All 117 rows | about 20 h | 17.4 GiB |
| Graph 43 or 196 (the Atlas 43 chain) | about 5.7 h | 14.5 GiB |
| The 19 graphs with compact four-root certificates (118 … 203) | 2.1–2.9 h each | 11.4 GiB |
| Graph 126 | 54 min | 8.8 GiB |
| Graphs 145, 148 | 11–12 min | 17.3 GiB |
| Any negative row | 3–5 min | 4.1–15.6 GiB |
| Any other row | 2–9 min | 3.5–7.9 GiB |

A single row's figure is for verifying that row alone from scratch, including every module it imports. On a machine with less than 32 GiB, verify rows individually with a cap a few GiB above the row's peak, for example `--rows 17 --memory-gib 8`. The fresh build directory takes about 19 GB of disk and can be deleted afterwards. The last step, `Taeyoung.Catalogue.Counts`, imports all 117 rows; Lean maps their `.olean` files copy-on-write and Windows charges the whole 22 GiB mapping to the process although only 5 GiB is ever resident, so that step needs the default 32 GiB cap even though no single row needs more than 18 GiB.

### The Atlas 43 chain

```sh
lake build Taeyoung.CheckAtlas43
```

prints the axioms of the four theorems of the graph 43 certificate chain and its cone consequence for graph 196. Its chain of about 1,100 modules should be built one module at a time, by `python tools/verify_catalogue.py --rows 43,196`, before this target is requested.

## What is trusted

A machine check proves the statements as written, so a reader should confirm that the statements say what the paper claims. The definitions to read are short:

| Definition | File |
|---|---|
| Graphons on an arbitrary probability space; homomorphism density `homDensity`; edge density | [Foundation/Graphon.lean](lean/Taeyoung/Foundation/Graphon.lean), [Foundation/HomDensity.lean](lean/Taeyoung/Foundation/HomDensity.lean) |
| The chromatic polynomial and chromatic number, by their defining properties | [Foundation/ChromaticPolynomial.lean](lean/Taeyoung/Foundation/ChromaticPolynomial.lean) |
| The target $\Phi_H$ and the admissible range $p\ge1-1/(\chi(H)-1)$ | [Foundation/ChromaticTarget.lean](lean/Taeyoung/Foundation/ChromaticTarget.lean), [Foundation/Status.lean](lean/Taeyoung/Foundation/Status.lean) |
| `SatisfiesLowerBound`, `ViolatesLowerBound` | [Foundation/Status.lean](lean/Taeyoung/Foundation/Status.lean) |
| `SatisfiesLowerBoundOn`, `EventuallySatisfiesLowerBound`, `TuranOptimal`, the Turán graphon `T_k` | [Paper/Basic.lean](lean/Taeyoung/Paper/Basic.lean) |
| Each row's graph, an explicit edge list on `Fin n` | [Examples/GraphNNN.lean](lean/Taeyoung/Examples/) |
| The 117 rows, their statuses and the counts | [Catalogue/Rows.lean](lean/Taeyoung/Catalogue/Rows.lean), [Catalogue/Counts.lean](lean/Taeyoung/Catalogue/Counts.lean) |
| The graphs of the general theorems: cycles, cones, disjoint unions, the generated class of trivially perfect graphs, $L_m$ | [Paper/OddCycles.lean](lean/Taeyoung/Paper/OddCycles.lean), [Paper/TriviallyPerfect.lean](lean/Taeyoung/Paper/TriviallyPerfect.lean), [Paper/ChordalLeaves.lean](lean/Taeyoung/Paper/ChordalLeaves.lean) |

Beyond these, the trusted base is the Lean 4 kernel, the pinned toolchain, Mathlib and the prebuilt `OddCycleBound`. The development declares no axioms and contains no `sorry`; every numerical certificate is checked by kernel computation (`decide +kernel`), never by `native_decide`, and the audits above confirm that each theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.

## Citation

```bibtex
@misc{Kim2026Goodman,
  author       = {Kim, Taeyoung},
  title        = {Goodman-type lower bounds for graph homomorphism densities},
  year         = {2026},
  howpublished = {\url{https://github.com/mekty2012/GoodmanTypeBound}},
  note         = {Paper and Lean 4 formalization}
}
```

The odd-cycle formalization imported as `OddCycleBound` is joint work of Im, Kim, and Yang; cite their paper (arXiv:2610.18277) and repository (<https://github.com/mekty2012/OddCycleGoodman-lean>) for Theorem 1.4.

## License

This repository is released under the MIT License; see [LICENSE](LICENSE).
