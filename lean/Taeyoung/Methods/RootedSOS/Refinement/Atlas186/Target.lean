import Taeyoung.Methods.RootedSOS.Induced.Six.Classification
import Taeyoung.Methods.RootedSOS.Induced.Six.Powers
import Taeyoung.Methods.RootedSOS.Induced.HomExpansion
import Taeyoung.Methods.RootedSOS.Induced.PatternCode
import Taeyoung.Methods.RootedSOS.Induced.Counts
import Taeyoung.Foundation.FiniteGraphEncoding

/-! Atlas 186: the homomorphism density on six sample points, expanded in the
156 induced densities, and the target polynomial `Φ_H`. -/

namespace Taeyoung.Methods.RootedSOS.Refinement.Atlas186.Target
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
open Finset MeasureTheory Taeyoung
open Taeyoung.Methods.RootedSOS.Induced Taeyoung.Methods.RootedSOS.Induced.Six
def graph : SimpleGraph (Fin 6) := graphFromEdges 6 [(0, 1), (0, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 5), (4, 5)]
instance : DecidableRel graph.Adj := by unfold graph; infer_instance
def presentIndex : Fin 10 → Fin 15 := ![0, 1, 6, 7, 8, 9, 10, 11, 13, 14]
def freeIndex : Fin 5 → Fin 15 := ![2, 3, 4, 5, 12]
def edgeMap : Fin 10 ⊕ Fin 5 → Fin 15 := Sum.elim presentIndex freeIndex
def edgeInv : Fin 15 → Fin 10 ⊕ Fin 5 := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inr 4, Sum.inl 8, Sum.inl 9]
private theorem edge_left : ∀ e, edgeInv (edgeMap e) = e := by decide +kernel
private theorem edge_right : ∀ e, edgeMap (edgeInv e) = e := by decide +kernel
def edgeEquiv : Fin 10 ⊕ Fin 5 ≃ Fin 15 := ⟨edgeMap,edgeInv,edge_left,edge_right⟩
private theorem present_injective : Function.Injective
    (fun i : Fin 10 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
private theorem edges_exact : graph.edgeFinset = univ.image
    (fun i : Fin 10 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
def completion (a : Fin 32) : Fin 32768 :=
  patternCode edgeEquiv (Sum.elim (fun _ => 1) (finFunctionFinEquiv.symm a))
private def histogramData : PackedTable := (.leaf (359293637669114504796544381610487473119170117444199559092492685117325679741038479101498378013481679932125156319010700386701481342268163287257035678308195718348364652343750273310221208418499664094960444736901642450309167377868910392317381212050702130300837509902147304569119544563757062231440791046849158700386043825984156186926216812497908920089277976773683100345011801491551775652986903303017438974768967954580628338939879079316798969837260082278754342475588556110071303019497505390531783013585721462246382375329713417130216380020649836125042170458552046358864866318905353086284547356496499032967585683015185847472010180218721814530118315560320718324876847174417582619377077152615595245603583758301636955805727130538806643703483135130926440710176))
def histogram (b : Fin 1) : Int := histogramData.get b
def countCode : Nat := 11772974680323550858780570727897517522771268271189392790067993946928195168839715180888997106375878104169644479817104909420034884203244137253289301031031884265370008925989266028434565443019353774341872823092024874762269936745573463544850939794283605740320988013886093196307525415615689049744815117230205243580793381424024852875950115673185257616229701756664778393375016226307727501616231062310277291244388222934034666324059823522482358247179817550693698344397467645552207334230961858927306795679026625585199040953811633825548699842140940908320444645037321834309061043643907208229852540480498686347209133960011995306219211276316312703596590861009740674738368223213072874736831799713141708713017083438642016173216739596514975071320134608190981380069720096
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
end Taeyoung.Methods.RootedSOS.Refinement.Atlas186.Target

namespace Taeyoung.Methods.RootedSOS.Refinement.Atlas186

/-- The target polynomial `Φ_H(p) = (1-p)^{v(H)} P_H(1/(1-p))` of Atlas 186. -/
noncomputable def target186 (p : Real) : Real :=
  (0)*p^0 + (4)*p^1 + (-27)*p^2 + (68)*p^3 + (-76)*p^4 + (32)*p^5 + (0)*p^6

end Taeyoung.Methods.RootedSOS.Refinement.Atlas186
