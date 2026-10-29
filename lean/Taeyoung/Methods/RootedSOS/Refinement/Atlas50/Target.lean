import Taeyoung.Methods.RootedSOS.Induced.Six.Classification
import Taeyoung.Methods.RootedSOS.Induced.Six.Powers
import Taeyoung.Methods.RootedSOS.Induced.HomExpansion
import Taeyoung.Methods.RootedSOS.Induced.PatternCode
import Taeyoung.Methods.RootedSOS.Induced.Counts
import Taeyoung.Foundation.FiniteGraphEncoding

/-! Atlas 50: the homomorphism density on six sample points, expanded in the
156 induced densities, and the target polynomial `Φ_H`. -/

namespace Taeyoung.Methods.RootedSOS.Refinement.Atlas50.Target
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
open Finset MeasureTheory Taeyoung
open Taeyoung.Methods.RootedSOS.Induced Taeyoung.Methods.RootedSOS.Induced.Six
def graph : SimpleGraph (Fin 6) := graphFromEdges 6 [(0, 1), (0, 3), (0, 4), (1, 2), (1, 4), (2, 3), (2, 4), (3, 4)]
instance : DecidableRel graph.Adj := by unfold graph; infer_instance
def presentIndex : Fin 8 → Fin 15 := ![0, 2, 3, 5, 7, 9, 10, 12]
def freeIndex : Fin 7 → Fin 15 := ![1, 4, 6, 8, 11, 13, 14]
def edgeMap : Fin 8 ⊕ Fin 7 → Fin 15 := Sum.elim presentIndex freeIndex
def edgeInv : Fin 15 → Fin 8 ⊕ Fin 7 := ![Sum.inl 0, Sum.inr 0, Sum.inl 1, Sum.inl 2, Sum.inr 1, Sum.inl 3, Sum.inr 2, Sum.inl 4, Sum.inr 3, Sum.inl 5, Sum.inl 6, Sum.inr 4, Sum.inl 7, Sum.inr 5, Sum.inr 6]
private theorem edge_left : ∀ e, edgeInv (edgeMap e) = e := by decide +kernel
private theorem edge_right : ∀ e, edgeMap (edgeInv e) = e := by decide +kernel
def edgeEquiv : Fin 8 ⊕ Fin 7 ≃ Fin 15 := ⟨edgeMap,edgeInv,edge_left,edge_right⟩
private theorem present_injective : Function.Injective
    (fun i : Fin 8 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
private theorem edges_exact : graph.edgeFinset = univ.image
    (fun i : Fin 8 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
def completion (a : Fin 128) : Fin 32768 :=
  patternCode edgeEquiv (Sum.elim (fun _ => 1) (finFunctionFinEquiv.symm a))
private def histogramData : PackedTable := (.leaf (359304601604298950893406882166414254051731193401987207090711681100389793029835905918098679855200599796065431611963072756834999974538063500763977260571611313394302926436599496779778830025822040435770090659343383615141209315762355321521692314622988678548643393500251624897572500138909698578384461926045430584860606309250685831500740627595952951312052746509513603266764375604888153665487807743409709498354685271917821360847856398883459555303221371574916194686493086853864030003520171472132517300924677171774513833928115584050825500882661867288879112613622288089983337097711313774777931368833637580770968624058229660196227915694272886565269630315353411781492409540976564095547755284947623641809017642896104945140837773735700837177406629634184142913664))
def histogram (b : Fin 1) : Int := histogramData.get b
def countCode : Nat := 11772974691287486043226667590398073449552200832265350577715992165924178232953003978315813706677719823089508420092397861792405017721876407153502807972614147680965054864263358877658035000640961096718213632737947316503434768787511356989780144105386178026869235819769691300627853868571264202381162060901084439852677855986508119405594690197000355660260924531434514223877937978881840837994243563214717683514911808651352003517081731499801924907765283511982994506249678550082951126957945881593388396413313964540908569085270232227715620451261802920351608481979476904550792162114686014190541033864511023485756937342953038350031935494051788254668626012324495707431824838775439433718307970391274040741413288872526610641206074707158171965513608531685484637771923584
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
end Taeyoung.Methods.RootedSOS.Refinement.Atlas50.Target

namespace Taeyoung.Methods.RootedSOS.Refinement.Atlas50

/-- The target polynomial `Φ_H(p) = (1-p)^{v(H)} P_H(1/(1-p))` of Atlas 50. -/
noncomputable def target50 (p : Real) : Real :=
  (0)*p^0 + (-3)*p^1 + (15)*p^2 + (-25)*p^3 + (14)*p^4 + (0)*p^5

end Taeyoung.Methods.RootedSOS.Refinement.Atlas50
