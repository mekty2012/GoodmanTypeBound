import Taeyoung.Methods.RootedSOS.Induced.Six.Classification
import Taeyoung.Methods.RootedSOS.Induced.Six.Powers
import Taeyoung.Methods.RootedSOS.Induced.HomExpansion
import Taeyoung.Methods.RootedSOS.Induced.PatternCode
import Taeyoung.Methods.RootedSOS.Induced.Counts
import Taeyoung.Foundation.FiniteGraphEncoding

/-! Atlas 143: the homomorphism density on six sample points, expanded in the
156 induced densities, and the target polynomial `Φ_H`. -/

namespace Taeyoung.Methods.RootedSOS.Refinement.Atlas143.Target
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
open Finset MeasureTheory Taeyoung
open Taeyoung.Methods.RootedSOS.Induced Taeyoung.Methods.RootedSOS.Induced.Six
def graph : SimpleGraph (Fin 6) := graphFromEdges 6 [(0, 1), (0, 2), (0, 4), (1, 3), (1, 5), (2, 3), (2, 5), (3, 5)]
instance : DecidableRel graph.Adj := by unfold graph; infer_instance
def presentIndex : Fin 8 → Fin 15 := ![0, 1, 3, 6, 8, 9, 11, 13]
def freeIndex : Fin 7 → Fin 15 := ![2, 4, 5, 7, 10, 12, 14]
def edgeMap : Fin 8 ⊕ Fin 7 → Fin 15 := Sum.elim presentIndex freeIndex
def edgeInv : Fin 15 → Fin 8 ⊕ Fin 7 := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inl 2, Sum.inr 1, Sum.inr 2, Sum.inl 3, Sum.inr 3, Sum.inl 4, Sum.inl 5, Sum.inr 4, Sum.inl 6, Sum.inr 5, Sum.inl 7, Sum.inr 6]
private theorem edge_left : ∀ e, edgeInv (edgeMap e) = e := by decide +kernel
private theorem edge_right : ∀ e, edgeMap (edgeInv e) = e := by decide +kernel
def edgeEquiv : Fin 8 ⊕ Fin 7 ≃ Fin 15 := ⟨edgeMap,edgeInv,edge_left,edge_right⟩
private theorem present_injective : Function.Injective
    (fun i : Fin 8 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
private theorem edges_exact : graph.edgeFinset = univ.image
    (fun i : Fin 8 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
def completion (a : Fin 128) : Fin 32768 :=
  patternCode edgeEquiv (Sum.elim (fun _ => 1) (finFunctionFinEquiv.symm a))
private def histogramData : PackedTable := (.leaf (359304601855232025140153646593152213370502801849969234002226954638892817631180970293256864718269248547063294683204981069448317578174857689770943664614504511178175046655227772379801735683234909626763099827505818231649713812356890184442553723825687734439154955061151081983692026422876618912610415445499908935107205443413096774009491949560857814160078090003520273877820042684825753724447654876385000438219477069459317450722505664670550342370884298169075334260655280128525460817596199901878234200514665554885564130211396517664813231979342901482574857431216393993190533346103577150015073218629352478899237945471287038785416486676824590540226740742112020912239941781496835738801250580300501552115505287329435647982362667032588815282206949630879523733632))
def histogram (b : Fin 1) : Int := histogramData.get b
def countCode : Nat := 11772974691287736976300914337162500187511519603873798559742903681197716735977605323380188864862582891738259417955469103700717631039480043947691814939018190574162838736383577505933635023546618509587404625747115478938051277292007951524643064966795380725925126331331252200084939988097548169301496286854603894331028102585642281816537198948322320565123772556778008230548549034548920775594302523061850658805851673443149545013171606149067711998552351174909588665389252712276225788388759957621818142130213554529291680135566515508649234438992899601385802177724294498656695369310934406453916271006360819200655065612274451407410524682622770806372600969434922466040955586307679953989951223886569393619323595360171043971908916232051468853491713332005481333152743552
def coefficient (g : Fin 156) : Int := decodeSignedDigit 65537 32768 countCode g
private theorem count_total : (countCode : Int) = 11772615386685881744275774183515907035298149101071948590508901454243077843159974142409895607997864622489712354660785898719648182721901869090002043995353576069651660561336922278161255221810935274677777862647287973119819627578195594634458622413071555038190687176376191049002956296071125292682583676439158394422092995380198868719763189456372759707309612478688004710274671214506235949840578075406974273805413453966080085695720883643403041448209980290611419590054992056996097262927942361421916263896013039863736794571436304112131569625760920258484319602866863282262702178777588302876766255933142189848176166374328980120371739266136093981782060742694180354020043346365898457154212422635989093117771479854883714536260933869384436264676431125055850453629009920 + ∑ b, histogram b := by decide +kernel
private theorem block_000 : histogram 0 =
    ∑ i : Fin 128, groupPower (host (completion (finProdFinEquiv ((0 : Fin 1),i)))) := by decide +kernel
theorem histogram_exact (b : Fin 1) : histogram b =
    ∑ i : Fin 128, groupPower (host (completion (finProdFinEquiv (b,i)))) := by
  fin_cases b
  · exact block_000

theorem countCode_exact : (countCode : Int) = (32768 : Int)*geometricEncoding 65537 156 +
    ∑ a : Fin 128, (65537 : Int)^(host (completion a)).1 := by
  rw [histogram_offset]
  rw [← (finProdFinEquiv : Fin 1 × Fin 128 ≃ Fin 128).sum_comp
    (fun a : Fin 128 => (65537 : Int)^(host (completion a)).1)]
  simp only [Fintype.sum_prod_type]
  simp_rw [← groupPower_exact, ← histogram_exact]
  exact count_total
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
theorem hom_expansion (W : Graphon Ω μ) : homDensity graph W =
    ∑ a : Fin 128, density (host (completion a)) W := by
  rw [homDensity_completions graph pairs edgeEquiv present_injective edges_exact W]
  rw [← finFunctionFinEquiv.symm.sum_comp (fun q : Fin 7 → Fin 2 =>
    inducedDensity pairs (fun i => Sum.elim (fun _ => 1) q (edgeEquiv.symm i)) W)]
  apply Finset.sum_congr rfl
  intro a _
  have h := inducedDensity_classification (completion a) W
  simpa only [completion, patternCode, bits, Equiv.symm_apply_apply] using h
theorem density_expansion (W : Graphon Ω μ) : homDensity graph W =
    ∑ g : Fin 156, (coefficient g : Real)*density g W := by
  rw [hom_expansion]
  exact count_density_sum (fun a : Fin 128 => host (completion a))
    (by decide) (by norm_num) countCode_exact (fun g => density g W)
#print axioms density_expansion
end Taeyoung.Methods.RootedSOS.Refinement.Atlas143.Target

namespace Taeyoung.Methods.RootedSOS.Refinement.Atlas143

/-- The target polynomial `Φ_H(p) = (1-p)^{v(H)} P_H(1/(1-p))` of Atlas 143. -/
noncomputable def target143 (p : Real) : Real :=
  (0)*p^0 + (0)*p^1 + (-2)*p^2 + (10)*p^3 + (-17)*p^4 + (10)*p^5 + (0)*p^6

end Taeyoung.Methods.RootedSOS.Refinement.Atlas143
