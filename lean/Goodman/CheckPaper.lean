import Goodman.Paper

/-!
# Axiom audit for the results of `paper.pdf`

One `#print axioms` line for each theorem listed in `Goodman/Paper.lean`.  Every
line must read `… depends on axioms: [propext, Classical.choice, Quot.sound]`.

Theorem 1.7 is audited row by row by `tools/verify_catalogue.py`
(it needs the whole catalogue, so it is not imported here).
-/

open Goodman.Paper

-- Section 1: Turán values and optimality at Turán densities
#print axioms Goodman.Paper.homDensity_turan_eq_chromaticTarget
#print axioms Goodman.Paper.edgeDensity_turan
#print axioms Goodman.Paper.turanOptimal_of_satisfiesLowerBound
#print axioms Goodman.Paper.TuranOptimal.le_of_le_edgeDensity
#print axioms Goodman.Paper.satisfiesLowerBound_of_edgeless

-- Section 2: Theorem 1.1, Lemma 1.2, Proposition 2.1,
-- Lemmas 2.2 and 2.3
#print axioms Goodman.Methods.PureChordal.pureChordal_satisfiesLowerBound
#print axioms Goodman.Paper.Profile.pure_profileMonotone
#print axioms Goodman.Paper.Profile.chordal_satisfiesLowerBound_of_profile
#print axioms Goodman.Paper.Profile.profileB_eq_sub
#print axioms Goodman.Paper.Profile.isChromaticPolynomial_profilePoly
#print axioms Goodman.Paper.Profile.isChromaticNumber_of_bags
#print axioms Goodman.Paper.Profile.chromaticTarget_profilePoly
#print axioms Goodman.Paper.Profile.gluing_inequality
#print axioms Goodman.Methods.PureChordal.cliqueDensity_moonMoser_succ
#print axioms Goodman.Methods.PureChordal.cliqueDensity_step_lower

-- Section 3: Lemma 3.1, Proposition 3.2,
-- (3.3), Theorem 1.4, Corollary 1.5
#print axioms Goodman.Methods.Link.weighted_rootedTriangle
#print axioms Goodman.Paper.lifting
#print axioms Goodman.Paper.iterated_lifting
#print axioms Goodman.Paper.oddCycle_bound
#print axioms Goodman.Paper.cycleGraph_satisfiesLowerBound
#print axioms Goodman.Paper.oddJoin_satisfiesLowerBound

-- Section 3.3: Theorem 1.3
#print axioms Goodman.Paper.IsTriviallyPerfect.satisfiesLowerBound

-- Section 4: Theorem 1.6 and its lemmas
#print axioms Goodman.Paper.Eventual.eventual_tfae
#print axioms Goodman.Paper.Eventual.eventual_tfae_of_not_bipartite
#print axioms Goodman.Paper.Eventual.satisfiesLowerBoundOn_threshold
#print axioms Goodman.Paper.Eventual.turanOptimal_of_odd_girth
#print axioms Goodman.Paper.Eventual.chromaticTarget_eq_forest_sum
#print axioms Goodman.Paper.Eventual.gamma_eq
#print axioms Goodman.Paper.Eventual.sum_powerset_eq_sum_forests
#print axioms Goodman.Paper.Eventual.forest_variance
#print axioms Goodman.Paper.Eventual.Mom_variance
#print axioms Goodman.Paper.Eventual.intervalInt_le_closing
#print axioms Goodman.Paper.Eventual.intervalInt_leading
#print axioms Goodman.Paper.Eventual.sum_intervalInt_le
#print axioms Goodman.Paper.Eventual.Qs_le_triangle
#print axioms Goodman.Paper.Eventual.cycle_comparison
#print axioms Goodman.Paper.Eventual.scalar_moment
#print axioms Goodman.Paper.Eventual.abs_ev_le
#print axioms Goodman.Paper.Eventual.hasSum_cyc
#print axioms Goodman.Paper.Eventual.tsum_weighted_le
#print axioms Goodman.Paper.Eventual.Ss_decomp
#print axioms Goodman.Paper.Eventual.card_cycleSets_le
#print axioms Goodman.Paper.Eventual.local_estimate
#print axioms Goodman.Paper.Eventual.local_of_small_degree
#print axioms Goodman.Paper.Eventual.Dfun_nonneg
#print axioms Goodman.Paper.Eventual.Dfun_superadd
#print axioms Goodman.Paper.Eventual.abs_remPoly_sub_le
#print axioms Goodman.Paper.Eventual.truncation
#print axioms Goodman.Paper.Eventual.not_turanOptimal_of_even_girth

-- Section 6: Proposition 6.1
#print axioms Goodman.Paper.leafTriangle_twenty_violates
