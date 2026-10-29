import Taeyoung.Methods.RootedSOS.Induced.Six.Classification
import Taeyoung.Methods.RootedSOS.Induced.Six.Powers
import Taeyoung.Methods.RootedSOS.Induced.HomExpansion
import Taeyoung.Methods.RootedSOS.Induced.PatternCode
import Taeyoung.Methods.RootedSOS.Induced.Counts
import Taeyoung.Foundation.FiniteGraphEncoding

/-! Atlas 184: the homomorphism density on six sample points, expanded in the
156 induced densities, and the target polynomial `Φ_H`. -/

namespace Taeyoung.Methods.RootedSOS.Refinement.Atlas184.Target
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
open Finset MeasureTheory Taeyoung
open Taeyoung.Methods.RootedSOS.Induced Taeyoung.Methods.RootedSOS.Induced.Six
def graph : SimpleGraph (Fin 6) := graphFromEdges 6 [(0, 1), (0, 3), (0, 4), (0, 5), (1, 2), (1, 5), (2, 3), (2, 5), (3, 4), (3, 5)]
instance : DecidableRel graph.Adj := by unfold graph; infer_instance
def presentIndex : Fin 10 → Fin 15 := ![0, 2, 3, 4, 5, 8, 9, 11, 12, 13]
def freeIndex : Fin 5 → Fin 15 := ![1, 6, 7, 10, 14]
def edgeMap : Fin 10 ⊕ Fin 5 → Fin 15 := Sum.elim presentIndex freeIndex
def edgeInv : Fin 15 → Fin 10 ⊕ Fin 5 := ![Sum.inl 0, Sum.inr 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inr 1, Sum.inr 2, Sum.inl 5, Sum.inl 6, Sum.inr 3, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inr 4]
private theorem edge_left : ∀ e, edgeInv (edgeMap e) = e := by decide +kernel
private theorem edge_right : ∀ e, edgeMap (edgeInv e) = e := by decide +kernel
def edgeEquiv : Fin 10 ⊕ Fin 5 ≃ Fin 15 := ⟨edgeMap,edgeInv,edge_left,edge_right⟩
private theorem present_injective : Function.Injective
    (fun i : Fin 10 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
private theorem edges_exact : graph.edgeFinset = univ.image
    (fun i : Fin 10 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
def completion (a : Fin 32) : Fin 32768 :=
  patternCode edgeEquiv (Sum.elim (fun _ => 1) (finFunctionFinEquiv.symm a))
private def histogramData : PackedTable := (.leaf (359293637669114504796544084464169169970526965722254314449145818980324695907199431853122176662925793224303679084561932213066415597383564940245079178074940776296765329938599232056099690788817673894462604970613035969059185551567714737844378436356491881486464994471080810287071579645469990377926776094624451252719530703937138524508052564089566567683977921851137067707406616560351749205086886837823610283770312696467820989808141623737529344807907298918716682117555841359652715422487631756416254095586226280040010943200686008812129541635499045994524386388995982874894367241549104438499087184500602302104882591913465566206062422703180028529703962125297777149705408692996002307600291582708372499373663330958880065977737193802330312526273307251142881968160))
def histogram (b : Fin 1) : Int := histogramData.get b
def countCode : Nat := 11772974680323550858780570727600371204468119628037670844823350600062058167855881341841748730174527548282936658339870460651861249137499252654942289074531651010427957326666860877393311321501724092351672325252258586155788686763747162349196466791507911530072173641370662129813243367650770762672961603215253018873345714910902805858287697508936849273877296456609855847342378621122796301589783162293812097415697224278776553516710691785026778977554788197910338306737109612837456915643364849053672680150108626090016834582379504798140381755302555757530314127253252278245577073144829851981204755020326690450478271256920893585937945328558797161810590446656305651797193051774591453156520022927571801490270853518214673416326911606578238594988957398363101596510978080
def coefficient (g : Fin 156) : Int := decodeSignedDigit 65537 32768 countCode g
private theorem count_total : (countCode : Int) = 11772615386685881744275774183515907035298149101071948590508901454243077843159974142409895607997864622489712354660785898719648182721901869090002043995353576069651660561336922278161255221810935274677777862647287973119819627578195594634458622413071555038190687176376191049002956296071125292682583676439158394422092995380198868719763189456372759707309612478688004710274671214506235949840578075406974273805413453966080085695720883643403041448209980290611419590054992056996097262927942361421916263896013039863736794571436304112131569625760920258484319602866863282262702178777588302876766255933142189848176166374328980120371739266136093981782060742694180354020043346365898457154212422635989093117771479854883714536260933869384436264676431125055850453629009920 + ∑ b, histogram b := by decide +kernel
private theorem block_000 : histogram 0 =
    ∑ i : Fin 32, groupPower (host (completion (finProdFinEquiv ((0 : Fin 1),i)))) := by decide +kernel
theorem histogram_exact (b : Fin 1) : histogram b =
    ∑ i : Fin 32, groupPower (host (completion (finProdFinEquiv (b,i)))) := by
  fin_cases b
  · exact block_000

theorem countCode_exact : (countCode : Int) = (32768 : Int)*geometricEncoding 65537 156 +
    ∑ a : Fin 32, (65537 : Int)^(host (completion a)).1 := by
  rw [histogram_offset]
  rw [← (finProdFinEquiv : Fin 1 × Fin 32 ≃ Fin 32).sum_comp
    (fun a : Fin 32 => (65537 : Int)^(host (completion a)).1)]
  simp only [Fintype.sum_prod_type]
  simp_rw [← groupPower_exact, ← histogram_exact]
  exact count_total
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
theorem hom_expansion (W : Graphon Ω μ) : homDensity graph W =
    ∑ a : Fin 32, density (host (completion a)) W := by
  rw [homDensity_completions graph pairs edgeEquiv present_injective edges_exact W]
  rw [← finFunctionFinEquiv.symm.sum_comp (fun q : Fin 5 → Fin 2 =>
    inducedDensity pairs (fun i => Sum.elim (fun _ => 1) q (edgeEquiv.symm i)) W)]
  apply Finset.sum_congr rfl
  intro a _
  have h := inducedDensity_classification (completion a) W
  simpa only [completion, patternCode, bits, Equiv.symm_apply_apply] using h
theorem density_expansion (W : Graphon Ω μ) : homDensity graph W =
    ∑ g : Fin 156, (coefficient g : Real)*density g W := by
  rw [hom_expansion]
  exact count_density_sum (fun a : Fin 32 => host (completion a))
    (by decide) (by norm_num) countCode_exact (fun g => density g W)
#print axioms density_expansion
end Taeyoung.Methods.RootedSOS.Refinement.Atlas184.Target

namespace Taeyoung.Methods.RootedSOS.Refinement.Atlas184

/-- The target polynomial `Φ_H(p) = (1-p)^{v(H)} P_H(1/(1-p))` of Atlas 184. -/
noncomputable def target184 (p : Real) : Real :=
  (0)*p^0 + (3)*p^1 + (-21)*p^2 + (55)*p^3 + (-64)*p^4 + (28)*p^5 + (0)*p^6

end Taeyoung.Methods.RootedSOS.Refinement.Atlas184
