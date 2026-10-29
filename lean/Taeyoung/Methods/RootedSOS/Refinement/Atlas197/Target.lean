import Taeyoung.Methods.RootedSOS.Induced.Six.Classification
import Taeyoung.Methods.RootedSOS.Induced.Six.Powers
import Taeyoung.Methods.RootedSOS.Induced.HomExpansion
import Taeyoung.Methods.RootedSOS.Induced.PatternCode
import Taeyoung.Methods.RootedSOS.Induced.Counts
import Taeyoung.Foundation.FiniteGraphEncoding

/-! Atlas 197: the homomorphism density on six sample points, expanded in the
156 induced densities, and the target polynomial `Φ_H`. -/

namespace Taeyoung.Methods.RootedSOS.Refinement.Atlas197.Target
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
open Finset MeasureTheory Taeyoung
open Taeyoung.Methods.RootedSOS.Induced Taeyoung.Methods.RootedSOS.Induced.Six
def graph : SimpleGraph (Fin 6) := graphFromEdges 6 [(0, 1), (0, 2), (0, 3), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 4), (3, 4), (4, 5)]
instance : DecidableRel graph.Adj := by unfold graph; infer_instance
def presentIndex : Fin 11 → Fin 15 := ![0, 1, 2, 4, 5, 6, 7, 8, 10, 12, 14]
def freeIndex : Fin 4 → Fin 15 := ![3, 9, 11, 13]
def edgeMap : Fin 11 ⊕ Fin 4 → Fin 15 := Sum.elim presentIndex freeIndex
def edgeInv : Fin 15 → Fin 11 ⊕ Fin 4 := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inr 1, Sum.inl 8, Sum.inr 2, Sum.inl 9, Sum.inr 3, Sum.inl 10]
private theorem edge_left : ∀ e, edgeInv (edgeMap e) = e := by decide +kernel
private theorem edge_right : ∀ e, edgeMap (edgeInv e) = e := by decide +kernel
def edgeEquiv : Fin 11 ⊕ Fin 4 ≃ Fin 15 := ⟨edgeMap,edgeInv,edge_left,edge_right⟩
private theorem present_injective : Function.Injective
    (fun i : Fin 11 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
private theorem edges_exact : graph.edgeFinset = univ.image
    (fun i : Fin 11 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
def completion (a : Fin 16) : Fin 32768 :=
  patternCode edgeEquiv (Sum.elim (fun _ => 1) (finFunctionFinEquiv.symm a))
private def histogramData : PackedTable := (.leaf (359288155617879838120306056999513250738890807750604338619005808067437598498190712804424280431945454142456708604319630817086740846281810510317875282043852605510917696024520156018756322368803367124095351317046244962185445727175774893474015944001106092852425527448945082142746031339047099923969701993270267399980359799050752701132224592996960640907076591194990798333011769658553169153646739179233648420562155297991521138207266268809166561283289001589766787472735435205623406855953341473181497130082726108170212400588738280473606412339736025811890455757319313517032891826989630079066765868729863547246007812846564567431462001950739974673250406511442615657470119745282083908836025475625521867901416243056143859876280237995517083474845020880257668612112))
def histogram (b : Fin 1) : Int := histogramData.get b
def countCode : Nat := 11772974674841499624113894489572906548548887991879699194847520460051145280758472333122700032278296567943854811369390218350465269462748150900512361870635619922257171479032946798317273978133304078044901957998605019364781813023922770409352096429015556144283539601903639994085099042102464339782507646141151664689492975739997919472464321680965756667950519555279199701073004226275894503009731722146153507453834016121378077216859090909671850614771263579613009356842464792431302886334798314763389445393143122589844964783836892850412043232173259994510131493322620601576219211669415292506845322699010919711723412382141826684939170728138044721756733993100691796635700816485643739238121258661464718639639381271126770680120810149622431781759905970076730711297622032
def coefficient (g : Fin 156) : Int := decodeSignedDigit 65537 32768 countCode g
private theorem count_total : (countCode : Int) = 11772615386685881744275774183515907035298149101071948590508901454243077843159974142409895607997864622489712354660785898719648182721901869090002043995353576069651660561336922278161255221810935274677777862647287973119819627578195594634458622413071555038190687176376191049002956296071125292682583676439158394422092995380198868719763189456372759707309612478688004710274671214506235949840578075406974273805413453966080085695720883643403041448209980290611419590054992056996097262927942361421916263896013039863736794571436304112131569625760920258484319602866863282262702178777588302876766255933142189848176166374328980120371739266136093981782060742694180354020043346365898457154212422635989093117771479854883714536260933869384436264676431125055850453629009920 + ∑ b, histogram b := by decide +kernel
private theorem block_000 : histogram 0 =
    ∑ i : Fin 16, groupPower (host (completion (finProdFinEquiv ((0 : Fin 1),i)))) := by decide +kernel
theorem histogram_exact (b : Fin 1) : histogram b =
    ∑ i : Fin 16, groupPower (host (completion (finProdFinEquiv (b,i)))) := by
  fin_cases b
  · exact block_000

theorem countCode_exact : (countCode : Int) = (32768 : Int)*geometricEncoding 65537 156 +
    ∑ a : Fin 16, (65537 : Int)^(host (completion a)).1 := by
  rw [histogram_offset]
  rw [← (finProdFinEquiv : Fin 1 × Fin 16 ≃ Fin 16).sum_comp
    (fun a : Fin 16 => (65537 : Int)^(host (completion a)).1)]
  simp only [Fintype.sum_prod_type]
  simp_rw [← groupPower_exact, ← histogram_exact]
  exact count_total
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
theorem hom_expansion (W : Graphon Ω μ) : homDensity graph W =
    ∑ a : Fin 16, density (host (completion a)) W := by
  rw [homDensity_completions graph pairs edgeEquiv present_injective edges_exact W]
  rw [← finFunctionFinEquiv.symm.sum_comp (fun q : Fin 4 → Fin 2 =>
    inducedDensity pairs (fun i => Sum.elim (fun _ => 1) q (edgeEquiv.symm i)) W)]
  apply Finset.sum_congr rfl
  intro a _
  have h := inducedDensity_classification (completion a) W
  simpa only [completion, patternCode, bits, Equiv.symm_apply_apply] using h
theorem density_expansion (W : Graphon Ω μ) : homDensity graph W =
    ∑ g : Fin 156, (coefficient g : Real)*density g W := by
  rw [hom_expansion]
  exact count_density_sum (fun a : Fin 16 => host (completion a))
    (by decide) (by norm_num) countCode_exact (fun g => density g W)
#print axioms density_expansion
end Taeyoung.Methods.RootedSOS.Refinement.Atlas197.Target

namespace Taeyoung.Methods.RootedSOS.Refinement.Atlas197

/-- The target polynomial `Φ_H(p) = (1-p)^{v(H)} P_H(1/(1-p))` of Atlas 197. -/
noncomputable def target197 (p : Real) : Real :=
  (0)*p^0 + (7)*p^1 + (-45)*p^2 + (108)*p^3 + (-115)*p^4 + (46)*p^5 + (0)*p^6

end Taeyoung.Methods.RootedSOS.Refinement.Atlas197
