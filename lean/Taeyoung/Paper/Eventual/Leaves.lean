import Taeyoung.Paper.Eventual.Kruskal

/-!
# Leaves of forests

Every forest integral in this formalization of Theorem 1.6 is
handled by removing the edges of the forest one leaf at a time (the paper
proves Lemma 4.3 with a branching random walk instead).  The one combinatorial input is
`exists_leaf_notMem`: a nonempty forest has a leaf outside any vertex set `R`
none of whose distinct members are joined in the forest.  The proof takes a
longest path; its two ends are distinct leaves joined by the path, so they are
not both in `R`.
-/

open Finset SimpleGraph

namespace Taeyoung.Paper.Eventual

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `ℓ` is a leaf of `S` hanging from `u`: `ℓu` is the only edge of `S` at `ℓ`. -/
def IsLeaf (S : Finset (Sym2 V)) (ℓ u : V) : Prop :=
  ℓ ≠ u ∧ s(ℓ, u) ∈ S ∧ ∀ e ∈ S, ℓ ∈ e → e = s(ℓ, u)

/-- The edges of a path are distinct, so there are as many as its length. -/
lemma card_edges_toFinset {G : SimpleGraph V} {u v : V} {p : G.Walk u v} (hp : p.IsPath) :
    p.edges.toFinset.card = p.length := by
  rw [List.toFinset_card_of_nodup hp.isTrail.edges_nodup, Walk.length_edges]

/-- The end of a non-extendable path in a forest is a leaf. -/
lemma isLeaf_of_maximal {F : Finset (Sym2 V)} (hF : IsForest F) (hnd : ∀ e ∈ F, ¬ e.IsDiag)
    {a b : V} {p : (graphOf F).Walk a b} (hp : p.IsPath) (hlen : 1 ≤ p.length)
    (hmax : ∀ c d (q : (graphOf F).Walk c d), q.IsPath → q.length ≤ p.length) :
    IsLeaf F b p.penultimate := by
  have hnil : ¬ p.Nil := Walk.not_nil_iff_lt_length.mpr hlen
  have hadj : (graphOf F).Adj p.penultimate b := Walk.adj_penultimate hnil
  obtain ⟨hmem, hne⟩ := graphOf_adj.mp hadj
  refine ⟨hne.symm, by rw [Sym2.eq_swap]; exact hmem, fun e he hbe ↦ ?_⟩
  obtain ⟨c, rfl⟩ := Sym2.mem_iff_exists.mp hbe
  have hbc : b ≠ c := fun h ↦ hnd _ he (by simp [h])
  have hadj' : (graphOf F).Adj b c := graphOf_adj.mpr ⟨he, hbc⟩
  by_cases hc : c ∈ p.support
  · rw [hF.eq_penultimate_of_adj_end hp hadj' hc]
  · have := hmax _ _ _ (hp.concat hc hadj')
    rw [Walk.length_concat] at this
    omega

/-- **A nonempty forest has a leaf outside any set of mutually unjoined vertices.** -/
theorem exists_leaf_notMem {F : Finset (Sym2 V)} (hF : IsForest F)
    (hnd : ∀ e ∈ F, ¬ e.IsDiag) (hne : F.Nonempty) (R : Set V)
    (hR : ∀ r₁ ∈ R, ∀ r₂ ∈ R, (graphOf F).Reachable r₁ r₂ → r₁ = r₂) :
    ∃ ℓ u, ℓ ∉ R ∧ IsLeaf F ℓ u := by
  classical
  let P : ℕ → Prop := fun k ↦ ∃ a b, ∃ p : (graphOf F).Walk a b, p.IsPath ∧ p.length = k
  obtain ⟨e, he⟩ := hne
  induction e using Sym2.inductionOn with
  | _ x y =>
  have hxy : x ≠ y := fun h ↦ hnd _ he (by simp [h])
  have hadj : (graphOf F).Adj x y := graphOf_adj.mpr ⟨he, hxy⟩
  have hP1 : P 1 := ⟨x, y, Walk.cons hadj Walk.nil, by simp [hxy], by simp⟩
  have hbound : ∀ k, P k → k ≤ Fintype.card V := by
    rintro k ⟨a, b, p, hp, rfl⟩
    exact hp.length_lt.le
  have h1 : 1 ≤ Fintype.card V := hbound 1 hP1
  set K := Nat.findGreatest P (Fintype.card V)
  have hK : P K := Nat.findGreatest_spec h1 hP1
  have hK1 : 1 ≤ K := Nat.le_findGreatest h1 hP1
  obtain ⟨a, b, p, hp, hpK⟩ := hK
  have hmax : ∀ c d (q : (graphOf F).Walk c d), q.IsPath → q.length ≤ p.length := by
    intro c d q hq
    rw [hpK]
    exact Nat.le_findGreatest (hbound _ ⟨c, d, q, hq, rfl⟩) ⟨c, d, q, hq, rfl⟩
  have hlen : 1 ≤ p.length := hpK ▸ hK1
  have hab : a ≠ b := by
    intro h
    subst h
    have := Walk.length_eq_zero_iff.mpr (Walk.isPath_iff_nil.mp hp)
    omega
  by_cases hb : b ∈ R
  · have ha : a ∉ R := fun ha ↦ hab (hR a ha b hb p.reachable)
    refine ⟨a, p.reverse.penultimate, ha, ?_⟩
    refine isLeaf_of_maximal hF hnd hp.reverse (by rwa [Walk.length_reverse]) ?_
    intro c d q hq
    rw [Walk.length_reverse]
    exact hmax c d q hq
  · exact ⟨b, p.penultimate, hb, isLeaf_of_maximal hF hnd hp hlen hmax⟩

/-- Every nonempty forest has a leaf. -/
lemma exists_leaf {F : Finset (Sym2 V)} (hF : IsForest F) (hnd : ∀ e ∈ F, ¬ e.IsDiag)
    (hne : F.Nonempty) : ∃ ℓ u, IsLeaf F ℓ u := by
  obtain ⟨ℓ, u, -, h⟩ := exists_leaf_notMem hF hnd hne ∅ (by simp)
  exact ⟨ℓ, u, h⟩

/-- Sub-forests are forests. -/
lemma IsForest.subset {F G : Finset (Sym2 V)} (hG : IsForest G) (h : F ⊆ G) : IsForest F :=
  hG.anti (graphOf_mono h)

end Taeyoung.Paper.Eventual
