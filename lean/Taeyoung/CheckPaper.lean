import Taeyoung.Paper

/-!
# Axiom audit for the results of `paper.pdf`

One `#print axioms` line for each theorem listed in `Taeyoung/Paper.lean`.  Every
line must read `… depends on axioms: [propext, Classical.choice, Quot.sound]`.

Theorem 1.7 is audited row by row by `tools/verify_catalogue.py`
(it needs the whole catalogue, so it is not imported here).
-/

open Taeyoung.Paper

-- Section 1: Turán values and optimality at Turán densities
#print axioms Taeyoung.Paper.homDensity_turan_eq_chromaticTarget
#print axioms Taeyoung.Paper.edgeDensity_turan
#print axioms Taeyoung.Paper.turanOptimal_of_satisfiesLowerBound
#print axioms Taeyoung.Paper.TuranOptimal.le_of_le_edgeDensity
#print axioms Taeyoung.Paper.satisfiesLowerBound_of_edgeless

-- Section 2: Theorem 1.1, Lemma 1.2, Proposition 2.1,
-- Lemmas 2.2 and 2.3
#print axioms Taeyoung.Methods.PureChordal.pureChordal_satisfiesLowerBound
#print axioms Taeyoung.Paper.Profile.pure_profileMonotone
#print axioms Taeyoung.Paper.Profile.chordal_satisfiesLowerBound_of_profile
#print axioms Taeyoung.Paper.Profile.profileB_eq_sub
#print axioms Taeyoung.Paper.Profile.isChromaticPolynomial_profilePoly
#print axioms Taeyoung.Paper.Profile.isChromaticNumber_of_bags
#print axioms Taeyoung.Paper.Profile.chromaticTarget_profilePoly
#print axioms Taeyoung.Paper.Profile.gluing_inequality
#print axioms Taeyoung.Methods.PureChordal.cliqueDensity_moonMoser_succ
#print axioms Taeyoung.Methods.PureChordal.cliqueDensity_step_lower

-- Section 3: Lemma 3.1, Proposition 3.2,
-- (3.3), Theorem 1.4, Corollary 1.5
#print axioms Taeyoung.Methods.Link.weighted_rootedTriangle
#print axioms Taeyoung.Paper.lifting
#print axioms Taeyoung.Paper.iterated_lifting
#print axioms Taeyoung.Paper.oddCycle_bound
#print axioms Taeyoung.Paper.cycleGraph_satisfiesLowerBound
#print axioms Taeyoung.Paper.oddJoin_satisfiesLowerBound

-- Section 3.3: Theorem 1.3
#print axioms Taeyoung.Paper.IsTriviallyPerfect.satisfiesLowerBound

-- Section 4: Theorem 1.6 and its lemmas
#print axioms Taeyoung.Paper.Eventual.eventual_tfae
#print axioms Taeyoung.Paper.Eventual.eventual_tfae_of_not_bipartite
#print axioms Taeyoung.Paper.Eventual.satisfiesLowerBoundOn_threshold
#print axioms Taeyoung.Paper.Eventual.turanOptimal_of_odd_girth
#print axioms Taeyoung.Paper.Eventual.chromaticTarget_eq_forest_sum
#print axioms Taeyoung.Paper.Eventual.gamma_eq
#print axioms Taeyoung.Paper.Eventual.sum_powerset_eq_sum_forests
#print axioms Taeyoung.Paper.Eventual.forest_variance
#print axioms Taeyoung.Paper.Eventual.Mom_variance
#print axioms Taeyoung.Paper.Eventual.intervalInt_le_closing
#print axioms Taeyoung.Paper.Eventual.intervalInt_leading
#print axioms Taeyoung.Paper.Eventual.sum_intervalInt_le
#print axioms Taeyoung.Paper.Eventual.Qs_le_triangle
#print axioms Taeyoung.Paper.Eventual.cycle_comparison
#print axioms Taeyoung.Paper.Eventual.scalar_moment
#print axioms Taeyoung.Paper.Eventual.abs_ev_le
#print axioms Taeyoung.Paper.Eventual.hasSum_cyc
#print axioms Taeyoung.Paper.Eventual.tsum_weighted_le
#print axioms Taeyoung.Paper.Eventual.Ss_decomp
#print axioms Taeyoung.Paper.Eventual.card_cycleSets_le
#print axioms Taeyoung.Paper.Eventual.local_estimate
#print axioms Taeyoung.Paper.Eventual.local_of_small_degree
#print axioms Taeyoung.Paper.Eventual.Dfun_nonneg
#print axioms Taeyoung.Paper.Eventual.Dfun_superadd
#print axioms Taeyoung.Paper.Eventual.abs_remPoly_sub_le
#print axioms Taeyoung.Paper.Eventual.truncation
#print axioms Taeyoung.Paper.Eventual.not_turanOptimal_of_even_girth

-- Section 6: Proposition 6.1
#print axioms Taeyoung.Paper.leafTriangle_twenty_violates
