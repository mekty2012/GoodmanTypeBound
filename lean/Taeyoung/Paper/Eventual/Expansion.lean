import Taeyoung.Paper.Eventual.Forests
import Taeyoung.Paper.TargetPolynomial
import Taeyoung.Paper.Turan

/-!
# The forest expansion (`paper.pdf`, Lemma 4.2)

Write `U = 1 - W` for the complementary graphon, `E = E(H)`, and
`I_F(U) = ∫ ∏_{e ∈ F} U_e ∏_{e ∈ B(F)} (1 - U_e)` for a forest `F ⊆ E`
(`intervalInt`).  Expanding `∏_{e ∈ E} (1 - U_e)` and grouping the subsets of `E`
into the Kruskal intervals `[F, F ∪ B(F)]` gives

* `homDensity_eq_sum_forests`: `t(H, W) = ∑_F (-1)^{|F|} I_F(1 - W)`.

For the block graphon `U_k = 1 - T_k` every interval with `B(F) ≠ ∅` vanishes and
every forest has density `k^{-|F|}`; since `t(H, T_k) = Φ_H(1 - 1/k)`, comparing
polynomials gives the forest form of the chromatic polynomial

* `chromaticTarget_eq_forest_sum`: `Ψ_H(q) = ∑_{B(F) = ∅} (-q)^{|F|}`, where
  `Ψ_H(q) = Φ_H(1 - q)` (4.4), for every real `q`;

and therefore, with `q = ∫ U`,

* `gamma_eq` (4.6):
  `t(H,W) - Φ_H(p) = ∑_{B(F) = ∅} (-1)^{|F|} (t(F,U) - q^{|F|}) + ∑_{B(F) ≠ ∅} (-1)^{|F|} I_F(U)`.
-/

open MeasureTheory Finset Polynomial

namespace Taeyoung.Paper.Eventual

open Taeyoung Taeyoung.Methods.PureChordal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The complementary graphon -/

/-- The complementary graphon `1 - W`. -/
def _root_.Taeyoung.Graphon.compl (W : Graphon Ω μ) : Graphon Ω μ where
  toFun x y := 1 - W x y
  measurable := measurable_const.sub W.measurable
  nonneg x y := sub_nonneg.mpr (W.le_one x y)
  le_one x y := by linarith [W.nonneg x y]
  symm x y := by rw [W.symm]

@[simp] lemma compl_apply (W : Graphon Ω μ) (x y : Ω) : W.compl x y = 1 - W x y := rfl

lemma edgeValue_compl (W : Graphon Ω μ) (x : V → Ω) (e : Sym2 V) :
    edgeValue W.compl x e = 1 - edgeValue W x e := by
  induction e using Sym2.inductionOn with
  | _ u v => simp

lemma degree_compl (W : Graphon Ω μ) (x : Ω) : degree W.compl x = 1 - degree W x := by
  unfold degree
  simp only [compl_apply]
  rw [integral_sub (integrable_const _) ((isBdd_row W x).integrable)]
  simp

lemma meanDeg_compl (W : Graphon Ω μ) : meanDeg W.compl = 1 - edgeDensity W := by
  unfold meanDeg
  simp_rw [degree_compl]
  rw [integral_sub (integrable_const _) (isBdd_degree W).integrable, integral_degree]
  simp [edgeDensity]

/-! ### The intervals -/

/-- `1 - U` on the closed edges `B`, `U` elsewhere. -/
noncomputable def closedKernel (U : Graphon Ω μ) (B : Finset (Sym2 V)) (e : Sym2 V) :
    Graphon Ω μ := by
  classical
  exact if e ∈ B then U.compl else U

lemma closedKernel_of_mem (U : Graphon Ω μ) {B : Finset (Sym2 V)} {e : Sym2 V} (h : e ∈ B) :
    closedKernel U B e = U.compl := by
  classical
  simp [closedKernel, h]

lemma closedKernel_of_notMem (U : Graphon Ω μ) {B : Finset (Sym2 V)} {e : Sym2 V}
    (h : e ∉ B) : closedKernel U B e = U := by
  classical
  simp [closedKernel, h]

/-- The forest density `t(F,U)`. -/
noncomputable def forestDens (U : Graphon Ω μ) (F : Finset (Sym2 V)) : ℝ :=
  wInt (fun _ ↦ U) F (fun _ ↦ BddFun.one)

/-- `I_F(U) = ∫ ∏_{e ∈ F} U_e ∏_{e ∈ B(F)} (1 - U_e)`. -/
noncomputable def intervalInt (E : Finset (Sym2 V)) (U : Graphon Ω μ) (F : Finset (Sym2 V)) :
    ℝ :=
  wInt (closedKernel U (closedEdges E F)) (F ∪ closedEdges E F) (fun _ ↦ BddFun.one)

lemma intervalInt_of_closedEdges_eq_empty {E F : Finset (Sym2 V)} (U : Graphon Ω μ)
    (h : closedEdges E F = ∅) : intervalInt E U F = forestDens U F := by
  unfold intervalInt forestDens
  rw [h, Finset.union_empty]
  exact wInt_congr_kernel (fun e _ ↦ closedKernel_of_notMem U (by simp)) _

lemma intervalInt_nonneg (E : Finset (Sym2 V)) (U : Graphon Ω μ) (F : Finset (Sym2 V)) :
    0 ≤ intervalInt E U F :=
  wInt_nonneg _ _ fun _ _ ↦ zero_le_one

lemma edgeProd_closedKernel (U : Graphon Ω μ) {F B : Finset (Sym2 V)} (hFB : Disjoint F B)
    (x : V → Ω) :
    edgeProd (closedKernel U B) (F ∪ B) x =
      (∏ e ∈ F, edgeValue U x e) * ∏ e ∈ B, (1 - edgeValue U x e) := by
  unfold edgeProd
  rw [Finset.prod_union hFB]
  congr 1
  · exact Finset.prod_congr rfl fun e he ↦ by
      rw [closedKernel_of_notMem U (Finset.disjoint_left.mp hFB he)]
  · exact Finset.prod_congr rfl fun e he ↦ by
      rw [closedKernel_of_mem U he, edgeValue_compl]

/-- **The pointwise forest expansion.** -/
theorem prod_one_sub_eq_sum_forests {E : Finset (Sym2 V)} (hE : ∀ e ∈ E, ¬ e.IsDiag)
    (a : Sym2 V → ℝ) :
    ∏ e ∈ E, (1 - a e) = ∑ F ∈ forests E,
      (-1) ^ F.card * ((∏ e ∈ F, a e) * ∏ e ∈ closedEdges E F, (1 - a e)) := by
  have h1 : ∏ e ∈ E, (1 - a e) = ∑ A ∈ E.powerset, ∏ e ∈ A, (-a e) := by
    have := Finset.prod_add (fun e ↦ -a e) (fun _ ↦ (1 : ℝ)) E
    simp only [Finset.prod_const_one, mul_one] at this
    rw [← this]
    exact Finset.prod_congr rfl fun e _ ↦ by ring
  rw [h1, sum_powerset_eq_sum_forests hE]
  refine Finset.sum_congr rfl fun F _ ↦ ?_
  have h2 : ∀ D ∈ (closedEdges E F).powerset, ∏ e ∈ F ∪ D, (-a e) =
      (∏ e ∈ F, (-a e)) * ∏ e ∈ D, (-a e) := by
    intro D hD
    exact Finset.prod_union ((disjoint_closedEdges E F).mono_right (Finset.mem_powerset.mp hD))
  rw [Finset.sum_congr rfl h2, ← Finset.mul_sum, Finset.prod_neg]
  have h3 : ∑ D ∈ (closedEdges E F).powerset, ∏ e ∈ D, (-a e) =
      ∏ e ∈ closedEdges E F, (1 - a e) := by
    have := Finset.prod_add (fun e ↦ -a e) (fun _ ↦ (1 : ℝ)) (closedEdges E F)
    simp only [Finset.prod_const_one, mul_one] at this
    rw [← this]
    exact Finset.prod_congr rfl fun e _ ↦ by ring
  rw [h3]
  ring

lemma not_isDiag_of_mem_edgeFinset (H : SimpleGraph V) [DecidableRel H.Adj] :
    ∀ e ∈ H.edgeFinset, ¬ e.IsDiag := fun e he ↦
  SimpleGraph.not_isDiag_of_mem_edgeSet H (SimpleGraph.mem_edgeFinset.mp he)

/-- **`t(H,W) = ∑_F (-1)^{|F|} I_F(1-W)`.** -/
theorem homDensity_eq_sum_forests (H : SimpleGraph V) [DecidableRel H.Adj] (W : Graphon Ω μ) :
    homDensity H W = ∑ F ∈ forests H.edgeFinset,
      (-1) ^ F.card * intervalInt H.edgeFinset W.compl F := by
  have hE := not_isDiag_of_mem_edgeFinset H
  have hpt : ∀ x, graphWeight H W x = ∑ F ∈ forests H.edgeFinset, (-1) ^ F.card *
      (edgeProd (closedKernel W.compl (closedEdges H.edgeFinset F))
        (F ∪ closedEdges H.edgeFinset F) x * vertexProd (fun _ ↦ BddFun.one) x) := by
    intro x
    have hW : ∀ e, edgeValue W x e = 1 - edgeValue W.compl x e := by
      intro e; rw [edgeValue_compl]; ring
    unfold graphWeight
    simp_rw [hW]
    rw [prod_one_sub_eq_sum_forests hE]
    refine Finset.sum_congr rfl fun F _ ↦ ?_
    rw [edgeProd_closedKernel _ (disjoint_closedEdges _ F)]
    simp [vertexProd, BddFun.one]
  unfold homDensity
  simp_rw [hpt]
  rw [integral_finsetSum _ fun F _ ↦ (integrable_integrand _ _ _).const_mul _]
  refine Finset.sum_congr rfl fun F _ ↦ ?_
  rw [integral_const_mul]
  rfl

/-! ### The block graphon `U_k = 1 - T_k` -/

/-- `U_k(x,y) = [x = y]` on `Fin k`. -/
noncomputable def blockGraphon (k : ℕ) [NeZero k] : Graphon (Fin k) (finiteUniformMeasure (Fin k)) :=
  (balancedMultipartiteGraphon k).compl

lemma blockGraphon_apply (k : ℕ) [NeZero k] (x y : Fin k) :
    blockGraphon k x y = if x = y then 1 else 0 := by
  by_cases h : x = y <;> simp [blockGraphon, h]

lemma degree_blockGraphon (k : ℕ) [NeZero k] (x : Fin k) :
    degree (blockGraphon k) x = 1 / k := by
  unfold degree
  rw [finiteUniform_integral]
  simp only [blockGraphon_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true, Fintype.card_fin]

/-- Colourings constant along the edges of `F` are constant on its components. -/
lemma eq_of_reachable_of_forall {F : Finset (Sym2 V)} {α : Type*} (x : V → α)
    (hx : ∀ u v, s(u, v) ∈ F → x u = x v) {a b : V} (h : (graphOf F).Reachable a b) :
    x a = x b := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons hadj p ih => exact (hx _ _ (graphOf_adj.mp hadj).1).trans ih

/-- For the block graphon every interval with a closed edge vanishes. -/
lemma intervalInt_blockGraphon_eq_zero (k : ℕ) [NeZero k] (E F : Finset (Sym2 V))
    (hB : closedEdges E F ≠ ∅) : intervalInt E (blockGraphon k) F = 0 := by
  classical
  unfold intervalInt wInt
  refine (integral_congr_ae (ae_of_all _ fun x ↦ ?_)).trans (integral_zero _ _)
  rw [edgeProd_closedKernel _ (disjoint_closedEdges E F)]
  by_cases hx : ∀ u v, s(u, v) ∈ F → x u = x v
  · obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hB
    obtain ⟨-, -, hc⟩ := mem_closedEdges.mp he
    induction e using Sym2.inductionOn with
    | _ a b =>
      have hab : x a = x b :=
        eq_of_reachable_of_forall x hx (reachable_mono (below_subset _ _) (closes_mk.mp hc))
      rw [Finset.prod_eq_zero he (by simp [blockGraphon_apply, hab])]
      simp
  · push_neg at hx
    obtain ⟨u, v, huv, hne⟩ := hx
    rw [Finset.prod_eq_zero huv (by simp [blockGraphon_apply, hne])]
    simp

/-! ### The forest form of the chromatic polynomial -/

open scoped Classical in
/-- The forests `F ⊆ E` with `B(F) = ∅`. -/
noncomputable def openForests (E : Finset (Sym2 V)) : Finset (Finset (Sym2 V)) :=
  (forests E).filter fun F ↦ closedEdges E F = ∅

lemma mem_openForests {E F : Finset (Sym2 V)} :
    F ∈ openForests E ↔ F ∈ forests E ∧ closedEdges E F = ∅ := by
  classical
  unfold openForests
  rw [Finset.mem_filter]

/-- `Φ_H(1 - 1/k) = ∑_{B(F)=∅} (-1/k)^{|F|}`. -/
theorem chromaticTarget_turan_forest (H : SimpleGraph V) [DecidableRel H.Adj]
    {P : ℝ[X]} (hP : IsChromaticPolynomial H P) (k : ℕ) [NeZero k] :
    chromaticTarget (V := V) P (1 - 1 / (k : ℝ)) =
      ∑ F ∈ openForests H.edgeFinset, (-(1 / (k : ℝ))) ^ F.card := by
  classical
  have hE := not_isDiag_of_mem_edgeFinset H
  rw [← homDensity_turan_eq_chromaticTarget hP k, homDensity_eq_sum_forests]
  have hcompl : (balancedMultipartiteGraphon k).compl = blockGraphon k := rfl
  rw [hcompl]
  rw [← Finset.sum_filter_add_sum_filter_not (forests H.edgeFinset)
    (fun F ↦ closedEdges H.edgeFinset F = ∅)]
  have hzero : ∑ F ∈ (forests H.edgeFinset).filter (fun F ↦ ¬ closedEdges H.edgeFinset F = ∅),
      (-1) ^ F.card * intervalInt H.edgeFinset (blockGraphon k) F = 0 :=
    Finset.sum_eq_zero fun F hF ↦ by
      rw [intervalInt_blockGraphon_eq_zero k _ _ (Finset.mem_filter.mp hF).2, mul_zero]
  rw [hzero, add_zero]
  unfold openForests
  refine Finset.sum_congr rfl fun F hF ↦ ?_
  obtain ⟨hFf, hB⟩ := Finset.mem_filter.mp hF
  obtain ⟨hFE, hfor⟩ := mem_forests.mp hFf
  rw [intervalInt_of_closedEdges_eq_empty _ hB, forestDens]
  have := wInt_forest_const (blockGraphon k) (degree_blockGraphon k) F.card F rfl hfor
    (fun e he ↦ hE e (hFE he)) (fun _ ↦ 1)
  have hone : (fun _ : V ↦ (BddFun.const (1 : ℝ) : BddFun (Fin k))) = fun _ ↦ BddFun.one :=
    rfl
  rw [hone] at this
  rw [this]
  simp only [Finset.prod_const_one, mul_one]
  ring

/-- **(4.4)**: `Ψ_H(q) = Φ_H(1 - q) = ∑_{B(F) = ∅} (-q)^{|F|}` for every `q`. -/
theorem chromaticTarget_eq_forest_sum (H : SimpleGraph V) [DecidableRel H.Adj]
    {P : ℝ[X]} (hP : IsChromaticPolynomial H P) (q : ℝ) :
    chromaticTarget (V := V) P (1 - q) =
      ∑ F ∈ openForests H.edgeFinset, (-q) ^ F.card := by
  rw [chromaticTarget_eq_eval_targetPoly hP]
  set ψ : ℝ[X] := ∑ F ∈ openForests H.edgeFinset, (-X) ^ F.card with hψ
  have hψeval : ∀ z, ψ.eval z = ∑ F ∈ openForests H.edgeFinset, (-z) ^ F.card := by
    intro z; simp [hψ, eval_finsetSum]
  have hpoly : (targetPoly (Fintype.card V) P).comp (1 - X) = ψ := by
    apply Polynomial.eq_of_infinite_eval_eq
    have hinf : Set.Infinite (Set.range fun k : ℕ ↦ (1 : ℝ) / ((k : ℝ) + 1)) := by
      refine Set.infinite_range_of_injective fun a b h ↦ ?_
      simp only [one_div, inv_inj] at h
      exact_mod_cast add_right_cancel h
    refine hinf.mono ?_
    rintro _ ⟨k, rfl⟩
    simp only [Set.mem_setOf_eq, eval_comp, eval_sub, eval_one, eval_X]
    rw [hψeval]
    have := chromaticTarget_turan_forest H hP (k + 1)
    rw [chromaticTarget_eq_eval_targetPoly hP] at this
    push_cast at this
    exact this
  have := congrArg (Polynomial.eval q) hpoly
  simp only [eval_comp, eval_sub, eval_one, eval_X] at this
  rw [this, hψeval]

/-! ### `Γ_H` -/

/-- **(4.6)**: with `U = 1 - W` and `q = ∫ U = 1 - p`,
`t(H,W) - Φ_H(p) = ∑_{B(F)=∅} (-1)^{|F|}(t(F,U) - q^{|F|}) + ∑_{B(F)≠∅} (-1)^{|F|} I_F(U)`. -/
theorem gamma_eq (H : SimpleGraph V) [DecidableRel H.Adj] {P : ℝ[X]}
    (hP : IsChromaticPolynomial H P) (W : Graphon Ω μ) :
    homDensity H W - chromaticTarget (V := V) P (edgeDensity W) =
      (∑ F ∈ openForests H.edgeFinset,
        (-1) ^ F.card * (forestDens W.compl F - meanDeg W.compl ^ F.card)) +
      ∑ F ∈ (forests H.edgeFinset).filter (fun F ↦ closedEdges H.edgeFinset F ≠ ∅),
        (-1) ^ F.card * intervalInt H.edgeFinset W.compl F := by
  classical
  have hp : edgeDensity W = 1 - meanDeg W.compl := by rw [meanDeg_compl]; ring
  rw [hp, chromaticTarget_eq_forest_sum H hP, homDensity_eq_sum_forests,
    ← Finset.sum_filter_add_sum_filter_not (forests H.edgeFinset)
      (fun F ↦ closedEdges H.edgeFinset F = ∅)]
  have hopen : (forests H.edgeFinset).filter (fun F ↦ closedEdges H.edgeFinset F = ∅) =
      openForests H.edgeFinset := by
    unfold openForests; congr
  rw [hopen]
  have h1 : ∑ F ∈ openForests H.edgeFinset, (-1) ^ F.card * intervalInt H.edgeFinset W.compl F =
      ∑ F ∈ openForests H.edgeFinset, (-1) ^ F.card * forestDens W.compl F :=
    Finset.sum_congr rfl fun F hF ↦ by
      rw [intervalInt_of_closedEdges_eq_empty _ (mem_openForests.mp hF).2]
  have h2 : ∑ F ∈ openForests H.edgeFinset, (-meanDeg W.compl) ^ F.card =
      ∑ F ∈ openForests H.edgeFinset, (-1) ^ F.card * meanDeg W.compl ^ F.card :=
    Finset.sum_congr rfl fun F _ ↦ by rw [neg_pow]
  rw [h1, h2]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

end Taeyoung.Paper.Eventual
