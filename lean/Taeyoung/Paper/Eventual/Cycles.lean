import Taeyoung.Paper.Eventual.Leaves
import Mathlib.Combinatorics.SimpleGraph.Girth

/-!
# Cycles, short paths, and the cycle count (`paper.pdf`, Lemma 4.11)

* `path_eq_of_length_add_lt_girth`: two paths with the same ends and total
  length below the girth coincide (their edges span an acyclic graph);
* `card_cycleSets_le`: **Lemma 4.11**, outer bound only.  If
  the girth `g` is odd and `g ≤ s`, the number of edge sets of `s`-cycles is at
  most `n^{s-g+3}` (the paper's (4.23) is the sharper
  `2s c_s ≤ n^{⌈s/h⌉} ≤ n^{s-g+3}`).  Instead of the paper's positions
  `0, h, 2h, …`, a cycle is recovered from its vertices at positions
  `0, 1, …, s-g+1` and `s-h` (`h = (g-1)/2`), because the two remaining arcs
  have length `h` and paths of length `≤ h` are unique.
-/

open Finset SimpleGraph

namespace Taeyoung.Paper.Eventual

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Walk bookkeeping -/

lemma mem_edgeSet_graphOf {S : Finset (Sym2 V)} {e : Sym2 V} :
    e ∈ (graphOf S).edgeSet ↔ e ∈ S ∧ ¬ e.IsDiag := by
  simp [graphOf, edgeSet_fromEdgeSet]

lemma edges_toFinset_subset_graphOf {S : Finset (Sym2 V)} {u v : V}
    (p : (graphOf S).Walk u v) : p.edges.toFinset ⊆ S := fun e he ↦
  (mem_edgeSet_graphOf.mp (p.edges_subset_edgeSet (List.mem_toFinset.mp he))).1

/-- The edges of a walk, read off its vertex sequence. -/
lemma edges_eq_map_getVert {G : SimpleGraph V} :
    ∀ {u v : V} (p : G.Walk u v),
      p.edges = (List.range p.length).map fun i ↦ s(p.getVert i, p.getVert (i + 1))
  | _, _, .nil => by simp
  | _, _, .cons h q => by
    rw [Walk.edges_cons, Walk.length_cons, List.range_succ_eq_map, List.map_cons,
      List.map_map, edges_eq_map_getVert q]
    simp only [Walk.getVert_zero, Walk.getVert_cons_succ, zero_add]
    congr 1

lemma length_eq_card_edges_toFinset {G : SimpleGraph V} {u v : V} {p : G.Walk u v}
    (hp : p.IsTrail) : p.length = p.edges.toFinset.card := by
  rw [List.toFinset_card_of_nodup hp.edges_nodup, Walk.length_edges]

/-! ### Short paths are unique -/

/-- **Short paths are unique.**  Two paths with the same ends whose lengths add
up to less than the girth coincide. -/
theorem path_eq_of_length_add_lt_girth (H : SimpleGraph V) {x y : V} {p q : H.Walk x y}
    (hp : p.IsPath) (hq : q.IsPath) (hlen : p.length + q.length < H.girth) : p = q := by
  classical
  by_cases hac : H.IsAcyclic
  · exact congrArg Subtype.val (hac.path_unique ⟨p, hp⟩ ⟨q, hq⟩)
  set S : Finset (Sym2 V) := (p.edges ++ q.edges).toFinset with hS
  have hSH : ∀ e ∈ S, e ∈ H.edgeSet := by
    intro e he
    rcases List.mem_append.mp (List.mem_toFinset.mp he) with h | h
    · exact p.edges_subset_edgeSet h
    · exact q.edges_subset_edgeSet h
  have hacyc : (graphOf S).IsAcyclic := by
    intro w c hc
    have hcH : (c.transfer H fun e he ↦ hSH e
        ((mem_edgeSet_graphOf.mp (c.edges_subset_edgeSet he)).1)).IsCycle := hc.transfer _
    have h1 := H.girth_le_length hcH
    rw [Walk.length_transfer] at h1
    have h2 : c.length ≤ S.card := by
      rw [length_eq_card_edges_toFinset hc.isTrail]
      exact Finset.card_le_card (edges_toFinset_subset_graphOf c)
    have h3 : S.card ≤ p.length + q.length := by
      refine (List.toFinset_card_le _).trans ?_
      simp
    omega
  have hpS : ∀ e ∈ p.edges, e ∈ (graphOf S).edgeSet := fun e he ↦
    mem_edgeSet_graphOf.mpr ⟨List.mem_toFinset.mpr (List.mem_append_left _ he),
      H.not_isDiag_of_mem_edgeSet (p.edges_subset_edgeSet he)⟩
  have hqS : ∀ e ∈ q.edges, e ∈ (graphOf S).edgeSet := fun e he ↦
    mem_edgeSet_graphOf.mpr ⟨List.mem_toFinset.mpr (List.mem_append_right _ he),
      H.not_isDiag_of_mem_edgeSet (q.edges_subset_edgeSet he)⟩
  have := hacyc.path_unique ⟨p.transfer _ hpS, hp.transfer hpS⟩ ⟨q.transfer _ hqS, hq.transfer hqS⟩
  have hsupp := congrArg (fun r : (graphOf S).Path x y ↦ r.1.support) this
  simp only [Walk.support_transfer] at hsupp
  exact Walk.ext_support hsupp

/-! ### Cycle edge sets -/

/-- `C` is the edge set of a cycle of `H`. -/
def IsCycleSet (H : SimpleGraph V) (C : Finset (Sym2 V)) : Prop :=
  ∃ (w : V) (c : H.Walk w w), c.IsCycle ∧ c.edges.toFinset = C

open scoped Classical in
/-- The edge sets of `s`-cycles of `H`. -/
noncomputable def cycleSets (H : SimpleGraph V) [DecidableRel H.Adj] (s : ℕ) :
    Finset (Finset (Sym2 V)) :=
  H.edgeFinset.powerset.filter fun C ↦ C.card = s ∧ IsCycleSet H C

lemma mem_cycleSets {H : SimpleGraph V} [DecidableRel H.Adj] {s : ℕ} {C : Finset (Sym2 V)} :
    C ∈ cycleSets H s ↔ C ⊆ H.edgeFinset ∧ C.card = s ∧ IsCycleSet H C := by
  classical
  unfold cycleSets
  rw [Finset.mem_filter, Finset.mem_powerset]

/-- A segment of a cycle avoiding the closing vertex is a path. -/
lemma isPath_segment {H : SimpleGraph V} {w : V} {c : H.Walk w w} (hc : c.IsCycle) {a ℓ : ℕ}
    (hal : a + ℓ ≤ c.length) (hwrap : a + ℓ ≤ c.length - 1 ∨ 1 ≤ a) :
    ((c.drop a).take ℓ).IsPath := by
  rw [← Walk.IsPath.getVert_injOn_iff]
  have hlen : ((c.drop a).take ℓ).length = ℓ := by
    rw [Walk.take_length, Walk.drop_length]; omega
  intro i hi j hj hij
  simp only [Set.mem_setOf_eq, hlen] at hi hj
  simp only [Walk.take_getVert, Walk.drop_getVert] at hij
  rw [min_eq_right hi, min_eq_right hj] at hij
  rcases hwrap with h | h
  · have := hc.getVert_injOn' (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) hij
    omega
  · have := hc.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) hij
    omega

/-- Two cycles agreeing at the ends of a short segment agree along it. -/
lemma getVert_eq_of_segment {H : SimpleGraph V} {w w' : V} {c : H.Walk w w} {c' : H.Walk w' w'}
    (hc : c.IsCycle) (hc' : c'.IsCycle) (hlen : c.length = c'.length) {a ℓ : ℕ}
    (hal : a + ℓ ≤ c.length) (hwrap : a + ℓ ≤ c.length - 1 ∨ 1 ≤ a)
    (hshort : ℓ + ℓ < H.girth) (h0 : c.getVert a = c'.getVert a)
    (h1 : c.getVert (a + ℓ) = c'.getVert (a + ℓ)) :
    ∀ i ≤ ℓ, c.getVert (a + i) = c'.getVert (a + i) := by
  have hP := isPath_segment hc hal hwrap
  have hP' := isPath_segment hc' (hlen ▸ hal) (hlen ▸ hwrap)
  have hend : (c'.drop a).getVert ℓ = (c.drop a).getVert ℓ := by
    rw [Walk.drop_getVert, Walk.drop_getVert, h1]
  have hP'c := (Walk.isPath_copy _ h0.symm hend).mpr hP'
  have hL : ((c.drop a).take ℓ).length = ℓ := by
    rw [Walk.take_length, Walk.drop_length]; omega
  have hL' : (((c'.drop a).take ℓ).copy h0.symm hend).length = ℓ := by
    rw [Walk.length_copy, Walk.take_length, Walk.drop_length]; omega
  have heq := path_eq_of_length_add_lt_girth H hP hP'c (by rw [hL, hL']; exact hshort)
  intro i hi
  have := congrArg (fun r ↦ r.getVert i) heq
  simp only [Walk.getVert_copy, Walk.take_getVert, Walk.drop_getVert, min_eq_right hi] at this
  exact this

/-- The length of a cycle with edge set `C` is `|C|`. -/
lemma length_eq_card_of_cycle {H : SimpleGraph V} {w : V} {c : H.Walk w w} (hc : c.IsCycle) :
    c.length = c.edges.toFinset.card :=
  length_eq_card_edges_toFinset hc.isTrail

/-- **Lemma 4.11**, outer bound: if `g = girth(H)` is odd and `g ≤ s`,
there are at most `n^{s-g+3}` edge sets of `s`-cycles (the paper also has the
factor `2s` and the intermediate bound `n^{⌈s/h⌉}`). -/
theorem card_cycleSets_le (H : SimpleGraph V) [DecidableRel H.Adj] (hodd : Odd H.girth)
    {s : ℕ} (hs : H.girth ≤ s) :
    (cycleSets H s).card ≤ Fintype.card V ^ (s - H.girth + 3) := by
  classical
  set g := H.girth with hg
  obtain ⟨h, hh⟩ := hodd
  have hg3 : 3 ≤ g := by
    have hne : g ≠ 0 := by omega
    have hcyc : ¬ H.IsAcyclic := fun hac ↦ hne (by rw [hg]; exact girth_eq_zero.mpr hac)
    exact three_le_girth hcyc
  have hh1 : 1 ≤ h := by omega
  -- a cycle for every cycle set
  have hchoose : ∀ C ∈ cycleSets H s, ∃ (w : V) (c : H.Walk w w), c.IsCycle ∧
      c.edges.toFinset = C := fun C hC ↦ (mem_cycleSets.mp hC).2.2
  let cyc : (C : Finset (Sym2 V)) → C ∈ cycleSets H s → Σ w : V, H.Walk w w :=
    fun C hC ↦ ⟨(hchoose C hC).choose, (hchoose C hC).choose_spec.choose⟩
  have hcyc : ∀ C (hC : C ∈ cycleSets H s), (cyc C hC).2.IsCycle ∧
      (cyc C hC).2.edges.toFinset = C := fun C hC ↦ (hchoose C hC).choose_spec.choose_spec
  have hlen : ∀ C (hC : C ∈ cycleSets H s), (cyc C hC).2.length = s := by
    intro C hC
    rw [length_eq_card_of_cycle (hcyc C hC).1, (hcyc C hC).2, (mem_cycleSets.mp hC).2.1]
  let k := s - g + 3
  let pos : Fin k → ℕ := fun j ↦ if (j : ℕ) ≤ s - g + 1 then j else s - h
  let rec_ : (cycleSets H s) → (Fin k → V) := fun C ↦ fun j ↦ (cyc C.1 C.2).2.getVert (pos j)
  have hinj : Function.Injective rec_ := by
    rintro ⟨C, hC1⟩ ⟨C', hC1'⟩ hrec
    rw [Subtype.mk.injEq]
    set c := (cyc C hC1).2
    set c' := (cyc C' hC1').2
    have hcc : c.IsCycle := (hcyc C hC1).1
    have hcc' : c'.IsCycle := (hcyc C' hC1').1
    have hl : c.length = s := hlen C hC1
    have hl' : c'.length = s := hlen C' hC1'
    have hagree : ∀ j : Fin k, c.getVert (pos j) = c'.getVert (pos j) := by
      intro j
      exact congrFun hrec j
    -- the vertices at positions `0, …, s-g+1`
    have hfront : ∀ i ≤ s - g + 1, c.getVert i = c'.getVert i := by
      intro i hi
      have := hagree ⟨i, by omega⟩
      simp only [pos, if_pos hi] at this
      exact this
    have hmid : c.getVert (s - h) = c'.getVert (s - h) := by
      have := hagree ⟨s - g + 2, by omega⟩
      simp only [pos, show ¬ s - g + 2 ≤ s - g + 1 by omega, if_false] at this
      exact this
    -- the first arc, from `s-g+1` to `s-h`
    have harc1 := getVert_eq_of_segment hcc hcc' (hl.trans hl'.symm) (a := s - g + 1) (ℓ := h)
      (by omega) (Or.inl (by omega)) (by omega) (hfront _ le_rfl)
      (by rw [show s - g + 1 + h = s - h by omega]; exact hmid)
    -- the second arc, from `s-h` to `s`
    have hend : c.getVert (s - h + h) = c'.getVert (s - h + h) := by
      rw [show s - h + h = s by omega, ← hl, Walk.getVert_length, hl, ← hl', Walk.getVert_length]
      have := hfront 0 (by omega)
      rwa [Walk.getVert_zero, Walk.getVert_zero] at this
    have harc2 := getVert_eq_of_segment hcc hcc' (hl.trans hl'.symm) (a := s - h) (ℓ := h)
      (by omega) (Or.inr (by omega)) (by omega) hmid hend
    have hall : ∀ i ≤ s, c.getVert i = c'.getVert i := by
      intro i hi
      by_cases h1 : i ≤ s - g + 1
      · exact hfront i h1
      · by_cases h2 : i ≤ s - h
        · have := harc1 (i - (s - g + 1)) (by omega)
          rwa [show s - g + 1 + (i - (s - g + 1)) = i by omega] at this
        · have := harc2 (i - (s - h)) (by omega)
          rwa [show s - h + (i - (s - h)) = i by omega] at this
    have hedges : c.edges = c'.edges := by
      rw [edges_eq_map_getVert c, edges_eq_map_getVert c', hl, hl']
      refine List.map_congr_left fun i hi ↦ ?_
      have hi' := List.mem_range.mp hi
      rw [hall i (by omega), hall (i + 1) (by omega)]
    rw [← (hcyc C hC1).2, ← (hcyc C' hC1').2]
    exact congrArg List.toFinset hedges
  have := Fintype.card_le_of_injective rec_ hinj
  simpa [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin] using this

end Taeyoung.Paper.Eventual
