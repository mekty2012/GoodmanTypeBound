import Taeyoung.Methods.RootedSOS.Induced.Six.Classification
import Taeyoung.Methods.RootedSOS.Induced.Six.Powers
import Taeyoung.Methods.RootedSOS.Induced.HomExpansion
import Taeyoung.Methods.RootedSOS.Induced.PatternCode
import Taeyoung.Methods.RootedSOS.Induced.Counts
import Taeyoung.Foundation.FiniteGraphEncoding

/-! Atlas 166: the homomorphism density on six sample points, expanded in the
156 induced densities, and the target polynomial `Φ_H`. -/

namespace Taeyoung.Methods.RootedSOS.Refinement.Atlas166.Target
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
open Finset MeasureTheory Taeyoung
open Taeyoung.Methods.RootedSOS.Induced Taeyoung.Methods.RootedSOS.Induced.Six
def graph : SimpleGraph (Fin 6) := graphFromEdges 6 [(0, 1), (0, 3), (0, 4), (0, 5), (1, 2), (1, 5), (2, 3), (3, 4), (3, 5)]
instance : DecidableRel graph.Adj := by unfold graph; infer_instance
def presentIndex : Fin 9 → Fin 15 := ![0, 2, 3, 4, 5, 8, 9, 12, 13]
def freeIndex : Fin 6 → Fin 15 := ![1, 6, 7, 10, 11, 14]
def edgeMap : Fin 9 ⊕ Fin 6 → Fin 15 := Sum.elim presentIndex freeIndex
def edgeInv : Fin 15 → Fin 9 ⊕ Fin 6 := ![Sum.inl 0, Sum.inr 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inr 1, Sum.inr 2, Sum.inl 5, Sum.inl 6, Sum.inr 3, Sum.inr 4, Sum.inl 7, Sum.inl 8, Sum.inr 5]
private theorem edge_left : ∀ e, edgeInv (edgeMap e) = e := by decide +kernel
private theorem edge_right : ∀ e, edgeMap (edgeInv e) = e := by decide +kernel
def edgeEquiv : Fin 9 ⊕ Fin 6 ≃ Fin 15 := ⟨edgeMap,edgeInv,edge_left,edge_right⟩
private theorem present_injective : Function.Injective
    (fun i : Fin 9 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
private theorem edges_exact : graph.edgeFinset = univ.image
    (fun i : Fin 9 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
def completion (a : Fin 64) : Fin 32768 :=
  patternCode edgeEquiv (Sum.elim (fun _ => 1) (finFunctionFinEquiv.symm a))
private def histogramData : PackedTable := (.leaf (359299119720350447764924774167907912952892419305911655467986664393424812817538400785910045554248104455070440056241496562465197705084996109530199820697751005907592565038307612625142322452388431394761956613732696422391519982176015785147381546187724772238824973284088594772808057897382170618415025151928202606927581552172585142630840640807923894198873839723094621190879367047828532092606013971957916662105758652567604139940683300007705000382211236587749944031247273206092526798860052123689999689854217713534941407382133422193283545360969926740818216733613300396590237071119488181168521423202466116865751158267002204272638698279297162246910440141089662957440358517125847169240215908040593773521510815786685044152550361106863488628768361365548898713664))
def histogram (b : Fin 1) : Int := histogramData.get b
def countCode : Nat := 11772974685805602094723539108290074943211101993491254502164369440907471267972791680810681518043418870594167425100842140216210647919606954086111574195174273820657568153901960585773880364133387663109172624603901705816242019098177770650243769794617742762962926001349475137597729104129022674853202091464310322624699922961751041304905820297013567631203811352527727804895862093873283778372670681420946231722075559724732653299860824326703049153210362501848007339999023304269303355454741221474039953895702894081450329512843686245553762909306281228411060421083596895563098769014659422364947424454565392314293032125487247122576011904834373278944307653134321443683000786724415583001381662851897133711545001365699501221305086419745543128165059893417216002527723584
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
end Taeyoung.Methods.RootedSOS.Refinement.Atlas166.Target

namespace Taeyoung.Methods.RootedSOS.Refinement.Atlas166

/-- The target polynomial `Φ_H(p) = (1-p)^{v(H)} P_H(1/(1-p))` of Atlas 166. -/
noncomputable def target166 (p : Real) : Real :=
  (0)*p^0 + (2)*p^1 + (-14)*p^2 + (37)*p^3 + (-44)*p^4 + (20)*p^5 + (0)*p^6

end Taeyoung.Methods.RootedSOS.Refinement.Atlas166
