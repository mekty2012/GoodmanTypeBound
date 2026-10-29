import Taeyoung.Paper.Eventual.TwoEdges

/-!
# Combinatorial preliminaries for the local estimate

* `exists_adjacent_open`: a graph with a cycle has two adjacent edges with no
  closed edge (`a ≥ 1` in Proposition 4.12);
* `cycleSets_girth_nonempty`, `cycleSets_eq_empty_of_lt_girth`: `c_g ≥ 1` and
  `c_s = 0` for `s < g`;
* `girth_le_card`, `card_edgeFinset_le`: `g ≤ n` and `m ≤ n²/2`;
* `one_add_pow_le`: `(1+Δ)^m ≤ 1 + 2mΔ` when `mΔ ≤ 1/2`.
-/

open MeasureTheory Finset SimpleGraph

namespace Taeyoung.Paper.Eventual

open Taeyoung

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {H : SimpleGraph V} [DecidableRel H.Adj]

lemma one_add_pow_le {Δ : ℝ} (hΔ0 : 0 ≤ Δ) {m : ℕ} (hm : (m : ℝ) * Δ ≤ 1 / 2) :
    (1 + Δ) ^ m ≤ 1 + 2 * m * Δ := by
  have key : ∀ k ≤ m, (1 + Δ) ^ k ≤ 1 + 2 * k * Δ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      have hkΔ : (k : ℝ) * Δ ≤ 1 / 2 := by
        have : (k : ℝ) ≤ m := by exact_mod_cast (by omega : k ≤ m)
        nlinarith
      rw [pow_succ]
      calc (1 + Δ) ^ k * (1 + Δ) ≤ (1 + 2 * k * Δ) * (1 + Δ) :=
            mul_le_mul_of_nonneg_right ih' (by linarith)
        _ ≤ 1 + 2 * ((k + 1 : ℕ) : ℝ) * Δ := by push_cast; nlinarith
  exact key m le_rfl

/-- A cycle of `H` has length at least the girth, so there are no shorter cycle sets. -/
lemma cycleSets_eq_empty_of_lt_girth {s : ℕ} (hs : s < H.girth) : cycleSets H s = ∅ := by
  ext C
  simp only [Finset.notMem_empty, iff_false]
  intro hC
  obtain ⟨-, hcard, w, c, hc, rfl⟩ := mem_cycleSets.mp hC
  have := H.girth_le_length hc
  rw [length_eq_card_of_cycle hc] at this
  omega

lemma cycleSets_girth_nonempty (hcyc : ¬ H.IsAcyclic) : (cycleSets H H.girth).Nonempty := by
  obtain ⟨w, c, hc, hlen⟩ := H.exists_girth_eq_length.mpr hcyc
  refine ⟨c.edges.toFinset, mem_cycleSets.mpr ⟨fun e he ↦ SimpleGraph.mem_edgeFinset.mpr
    (c.edges_subset_edgeSet (List.mem_toFinset.mp he)), ?_, w, c, hc, rfl⟩⟩
  rw [← length_eq_card_of_cycle hc, hlen]

lemma girth_le_card (hcyc : ¬ H.IsAcyclic) : H.girth ≤ Fintype.card V := by
  obtain ⟨C, hC⟩ := cycleSets_girth_nonempty hcyc
  have := card_le_of_mem_cycleSets hC
  rwa [(mem_cycleSets.mp hC).2.1] at this

lemma card_edgeFinset_le : (H.edgeFinset.card : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 / 2 := by
  have h := H.card_edgeFinset_le_card_choose_two
  have h' : (H.edgeFinset.card : ℝ) ≤ ((Fintype.card V).choose 2 : ℕ) := by exact_mod_cast h
  rw [Nat.cast_choose_two] at h'
  nlinarith [(Nat.cast_nonneg (Fintype.card V) : (0 : ℝ) ≤ Fintype.card V)]

/-- Two distinct edges never contain a cycle. -/
lemma isForest_of_card_le_two {F : Finset (Sym2 V)} (hF : F.card ≤ 2) : IsForest F := by
  intro w c hc
  have h1 := hc.three_le_length
  rw [length_eq_card_of_cycle hc] at h1
  have h2 := Finset.card_le_card (edges_toFinset_subset_graphOf c)
  omega

lemma ClosingPath.u_mem {F : Finset (Sym2 V)} {e : Sym2 V} (cp : ClosingPath H F e) :
    cp.u ∈ e := by
  cases cp with
  | mk u v p e_eq ne isPath edges_mem =>
    show u ∈ e
    rw [e_eq]; exact Sym2.mem_mk_left u v

lemma exists_first_edge {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (h : ¬ p.Nil) :
    ∃ x, s(u, x) ∈ p.edges := by
  cases p with
  | nil => exact absurd Walk.Nil.nil h
  | @cons _ b _ hadj q => exact ⟨b, by rw [Walk.edges_cons]; exact List.mem_cons.mpr (Or.inl rfl)⟩

/-- **`a ≥ 1`**: some pair of adjacent edges has no closed edge. -/
theorem exists_adjacent_open (hcyc : ¬ H.IsAcyclic) :
    ∃ F ∈ openForests H.edgeFinset, F.card = 2 ∧ ∃ v, ∀ f ∈ F, v ∈ f := by
  classical
  set E := H.edgeFinset
  set AP := E.powerset.filter fun F : Finset (Sym2 V) ↦ F.card = 2 ∧ ∃ v, ∀ f ∈ F, v ∈ f
  -- a cycle provides an adjacent pair
  have hAP : AP.Nonempty := by
    obtain ⟨w, c, hc, -⟩ := H.exists_girth_eq_length.mpr hcyc
    have h3 := hc.three_le_length
    have hadj1 := c.adj_getVert_succ (i := 0) (by omega)
    have hadj2 := c.adj_getVert_succ (i := 1) (by omega)
    have h02 : c.getVert 0 ≠ c.getVert 2 := by
      intro h
      have := hc.getVert_injOn' (by simp only [Set.mem_setOf_eq]; omega)
        (by simp only [Set.mem_setOf_eq]; omega) h
      omega
    refine ⟨{s(c.getVert 0, c.getVert 1), s(c.getVert 1, c.getVert 2)}, ?_⟩
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, ?_, c.getVert 1, ?_⟩
    · intro f hf
      rcases Finset.mem_insert.mp hf with h | h
      · rw [h]; exact SimpleGraph.mem_edgeFinset.mpr hadj1
      · rw [Finset.mem_singleton.mp h]; exact SimpleGraph.mem_edgeFinset.mpr hadj2
    · refine Finset.card_pair fun h ↦ ?_
      rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hadj1.ne h1
      · exact h02 h1
    · intro f hf
      rcases Finset.mem_insert.mp hf with h | h
      · rw [h]; simp
      · rw [Finset.mem_singleton.mp h]; simp
  obtain ⟨F, hF, hmax⟩ := AP.exists_max_image (fun F ↦ F.sup ord) hAP
  rw [Finset.mem_filter, Finset.mem_powerset] at hF
  obtain ⟨hFE, hcard, v, hv⟩ := hF
  refine ⟨F, mem_openForests.mpr ⟨mem_forests.mpr ⟨hFE, isForest_of_card_le_two hcard.le⟩, ?_⟩,
    hcard, v, hv⟩
  -- no closed edge
  by_contra hB
  obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hB
  obtain ⟨cp⟩ := exists_closingPath hFE he
  obtain ⟨heE, heF, -⟩ := mem_closedEdges.mp he
  have hg3 := H.three_le_girth hcyc
  have hlen := cp.girth_le heE
  have hPF : cp.edgeSet' = F := by
    refine Finset.eq_of_subset_of_card_le cp.edgeSet'_subset ?_
    rw [cp.card_edgeSet']; omega
  -- the first edge of the closing path
  have hnil : ¬ cp.p.Nil := Walk.not_nil_of_ne cp.ne
  obtain ⟨x, hx⟩ := exists_first_edge cp.p hnil
  have hf0F : s(cp.u, x) ∈ F := cp.edgeSet'_subset (List.mem_toFinset.mpr hx)
  have hord : ∀ f ∈ F, ord f < ord e := fun f hf ↦ cp.ord_lt (by rw [hPF]; exact hf)
  -- `{e, s(u, x)}` is an adjacent pair beating `F`
  have hG : ({e, s(cp.u, x)} : Finset (Sym2 V)) ∈ AP := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.insert_subset heE (Finset.singleton_subset_iff.mpr (hFE hf0F)),
      Finset.card_pair fun h ↦ heF (h ▸ hf0F), cp.u, fun f hf ↦ ?_⟩
    rcases Finset.mem_insert.mp hf with h | h
    · rw [h]; exact cp.u_mem
    · rw [Finset.mem_singleton.mp h]; simp
  have h1 := hmax _ hG
  have h2 : F.sup ord < ord e := by
    rw [Finset.sup_lt_iff (lt_of_le_of_lt (Nat.zero_le _) (hord _ hf0F))]
    exact hord
  have h3 : ord e ≤ ({e, s(cp.u, x)} : Finset (Sym2 V)).sup ord :=
    Finset.le_sup (Finset.mem_insert_self _ _)
  omega

end Taeyoung.Paper.Eventual
