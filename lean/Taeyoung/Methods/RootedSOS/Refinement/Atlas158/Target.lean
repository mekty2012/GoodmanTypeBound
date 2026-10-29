import Taeyoung.Methods.RootedSOS.Induced.Six.Classification
import Taeyoung.Methods.RootedSOS.Induced.Six.Powers
import Taeyoung.Methods.RootedSOS.Induced.HomExpansion
import Taeyoung.Methods.RootedSOS.Induced.PatternCode
import Taeyoung.Methods.RootedSOS.Induced.Counts
import Taeyoung.Foundation.FiniteGraphEncoding

/-! Atlas 158: the homomorphism density on six sample points, expanded in the
156 induced densities, and the target polynomial `Φ_H`. -/

namespace Taeyoung.Methods.RootedSOS.Refinement.Atlas158.Target
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
open Finset MeasureTheory Taeyoung
open Taeyoung.Methods.RootedSOS.Induced Taeyoung.Methods.RootedSOS.Induced.Six
def graph : SimpleGraph (Fin 6) := graphFromEdges 6 [(0, 1), (0, 3), (0, 4), (1, 2), (1, 4), (2, 3), (2, 4), (3, 4), (4, 5)]
instance : DecidableRel graph.Adj := by unfold graph; infer_instance
def presentIndex : Fin 9 → Fin 15 := ![0, 2, 3, 5, 7, 9, 10, 12, 14]
def freeIndex : Fin 6 → Fin 15 := ![1, 4, 6, 8, 11, 13]
def edgeMap : Fin 9 ⊕ Fin 6 → Fin 15 := Sum.elim presentIndex freeIndex
def edgeInv : Fin 15 → Fin 9 ⊕ Fin 6 := ![Sum.inl 0, Sum.inr 0, Sum.inl 1, Sum.inl 2, Sum.inr 1, Sum.inl 3, Sum.inr 2, Sum.inl 4, Sum.inr 3, Sum.inl 5, Sum.inl 6, Sum.inr 4, Sum.inl 7, Sum.inr 5, Sum.inl 8]
private theorem edge_left : ∀ e, edgeInv (edgeMap e) = e := by decide +kernel
private theorem edge_right : ∀ e, edgeMap (edgeInv e) = e := by decide +kernel
def edgeEquiv : Fin 9 ⊕ Fin 6 ≃ Fin 15 := ⟨edgeMap,edgeInv,edge_left,edge_right⟩
private theorem present_injective : Function.Injective
    (fun i : Fin 9 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
private theorem edges_exact : graph.edgeFinset = univ.image
    (fun i : Fin 9 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
def completion (a : Fin 64) : Fin 32768 :=
  patternCode edgeEquiv (Sum.elim (fun _ => 1) (finFunctionFinEquiv.symm a))
private def histogramData : PackedTable := (.leaf (359299119553061731593935670853712547931979183234455003269834200667949435594903012200700204428679866353732489286710397495614566061672941913127604497684878362965528345498218127000771853548857284455975849394690762760193172710016946241547950781425071976527590312323671469743018049372871620081774361968648886456846446043254052799478460562404894472940877472945230760802100550208660304931093440510828940454280518184927938197959521443718656422894221746571299550556249572151576017219946246916398142164384466733699331078566720929290136900556996420848732581848979310481068855509221011994154273097116832660706027833358731987023994837165284768691908302339755886798068538527588962303448261669067842640520989229864595734909358134981964638031530847773860081369152))
def histogram (b : Fin 1) : Int := histogramData.get b
def countCode : Nat := 11772974685805434806007368119186760747846081080255183045512171288443745792595569045422096308202293302356066087150072609117143797287963542031915171599851260948014626089682420496288255993664484131962233838496682663882579820750905611580700170363852980110167214766688514720472699314120498164302665450801127043308549841826242122772562667916935164601782553356160949941035473315056444610145509168847485102745867734484265013633918843164846760104632874512357990889605548306568248838945162307668832662038177424330470493902514870833060859762661477254905168335448712261573183247633097523888760410206239306680836872402162338852358763260973259266550752650996520109906841414904426046116515870897658160960412000844113579131995843227519418229314462655903624313710379072
def coefficient (g : Fin 156) : Int := decodeSignedDigit 65537 32768 countCode g
private theorem count_total : (countCode : Int) = 11772615386685881744275774183515907035298149101071948590508901454243077843159974142409895607997864622489712354660785898719648182721901869090002043995353576069651660561336922278161255221810935274677777862647287973119819627578195594634458622413071555038190687176376191049002956296071125292682583676439158394422092995380198868719763189456372759707309612478688004710274671214506235949840578075406974273805413453966080085695720883643403041448209980290611419590054992056996097262927942361421916263896013039863736794571436304112131569625760920258484319602866863282262702178777588302876766255933142189848176166374328980120371739266136093981782060742694180354020043346365898457154212422635989093117771479854883714536260933869384436264676431125055850453629009920 + ∑ b, histogram b := by decide +kernel
private theorem block_000 : histogram 0 =
    ∑ i : Fin 64, groupPower (host (completion (finProdFinEquiv ((0 : Fin 1),i)))) := by decide +kernel
theorem histogram_exact (b : Fin 1) : histogram b =
    ∑ i : Fin 64, groupPower (host (completion (finProdFinEquiv (b,i)))) := by
  fin_cases b
  · exact block_000

theorem countCode_exact : (countCode : Int) = (32768 : Int)*geometricEncoding 65537 156 +
    ∑ a : Fin 64, (65537 : Int)^(host (completion a)).1 := by
  rw [histogram_offset]
  rw [← (finProdFinEquiv : Fin 1 × Fin 64 ≃ Fin 64).sum_comp
    (fun a : Fin 64 => (65537 : Int)^(host (completion a)).1)]
  simp only [Fintype.sum_prod_type]
  simp_rw [← groupPower_exact, ← histogram_exact]
  exact count_total
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
theorem hom_expansion (W : Graphon Ω μ) : homDensity graph W =
    ∑ a : Fin 64, density (host (completion a)) W := by
  rw [homDensity_completions graph pairs edgeEquiv present_injective edges_exact W]
  rw [← finFunctionFinEquiv.symm.sum_comp (fun q : Fin 6 → Fin 2 =>
    inducedDensity pairs (fun i => Sum.elim (fun _ => 1) q (edgeEquiv.symm i)) W)]
  apply Finset.sum_congr rfl
  intro a _
  have h := inducedDensity_classification (completion a) W
  simpa only [completion, patternCode, bits, Equiv.symm_apply_apply] using h
theorem density_expansion (W : Graphon Ω μ) : homDensity graph W =
    ∑ g : Fin 156, (coefficient g : Real)*density g W := by
  rw [hom_expansion]
  exact count_density_sum (fun a : Fin 64 => host (completion a))
    (by decide) (by norm_num) countCode_exact (fun g => density g W)
#print axioms density_expansion
end Taeyoung.Methods.RootedSOS.Refinement.Atlas158.Target

namespace Taeyoung.Methods.RootedSOS.Refinement.Atlas158

/-- The target polynomial `Φ_H(p) = (1-p)^{v(H)} P_H(1/(1-p))` of Atlas 158. -/
noncomputable def target158 (p : Real) : Real :=
  (0)*p^0 + (0)*p^1 + (-3)*p^2 + (15)*p^3 + (-25)*p^4 + (14)*p^5 + (0)*p^6

end Taeyoung.Methods.RootedSOS.Refinement.Atlas158
