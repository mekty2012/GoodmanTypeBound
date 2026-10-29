import Taeyoung.Methods.RootedSOS.Induced.Six.Classification
import Taeyoung.Methods.RootedSOS.Induced.Six.Powers
import Taeyoung.Methods.RootedSOS.Induced.HomExpansion
import Taeyoung.Methods.RootedSOS.Induced.PatternCode
import Taeyoung.Methods.RootedSOS.Induced.Counts
import Taeyoung.Foundation.FiniteGraphEncoding

/-! Atlas 159: the homomorphism density on six sample points, expanded in the
156 induced densities, and the target polynomial `Φ_H`. -/

namespace Taeyoung.Methods.RootedSOS.Refinement.Atlas159.Target
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
open Finset MeasureTheory Taeyoung
open Taeyoung.Methods.RootedSOS.Induced Taeyoung.Methods.RootedSOS.Induced.Six
def graph : SimpleGraph (Fin 6) := graphFromEdges 6 [(0, 2), (1, 2), (1, 3), (1, 4), (2, 3), (2, 5), (3, 4), (3, 5), (4, 5)]
instance : DecidableRel graph.Adj := by unfold graph; infer_instance
def presentIndex : Fin 9 → Fin 15 := ![1, 5, 6, 7, 9, 11, 12, 13, 14]
def freeIndex : Fin 6 → Fin 15 := ![0, 2, 3, 4, 8, 10]
def edgeMap : Fin 9 ⊕ Fin 6 → Fin 15 := Sum.elim presentIndex freeIndex
def edgeInv : Fin 15 → Fin 9 ⊕ Fin 6 := ![Sum.inr 0, Sum.inl 0, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inr 4, Sum.inl 4, Sum.inr 5, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8]
private theorem edge_left : ∀ e, edgeInv (edgeMap e) = e := by decide +kernel
private theorem edge_right : ∀ e, edgeMap (edgeInv e) = e := by decide +kernel
def edgeEquiv : Fin 9 ⊕ Fin 6 ≃ Fin 15 := ⟨edgeMap,edgeInv,edge_left,edge_right⟩
private theorem present_injective : Function.Injective
    (fun i : Fin 9 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
private theorem edges_exact : graph.edgeFinset = univ.image
    (fun i : Fin 9 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
def completion (a : Fin 64) : Fin 32768 :=
  patternCode edgeEquiv (Sum.elim (fun _ => 1) (finFunctionFinEquiv.symm a))
private def histogramData : PackedTable := (.leaf (359299119636706089689167410215286039146161679422061531452616598571536284113407178066348357907205364444026681125655603553660763253475451471587019779683220910122269917822740996672324842887049811806469308597261586161957105993869814666362448097679435835166882661498969902270466135196370223950323330807799073710534656343974439805233173963526300739472026209086777052435389415410514535509503960834340349881119493741177985606477797415413114590938262788126645319443359603345722064999466922201101329660374701327039241416653319267759552315692413918555768266761751742256873835603185014069501807254399545316678500610173069206376694922896226834415609572294886765976324032833290477942302049636418734795705126054537983463011301855153895870715346351735649318600768))
def histogram (b : Fin 1) : Int := histogramData.get b
def countCode : Nat := 11772974685805518450365463350926122321337295262751370652040354070841649379444087549587961956355771827854156381341911554323201843485155344541473631015133259290561782831254745019157927546653822324489584331955885234705981584684189464449124984861169234474025854059037690018905226762206321662906533999769966193495803530036542843159568422630336286008049084504897091487327106603921646464376087579367808614155294573459821263681327361440818454562800918553399546235374435416599442984992941828344117365225673414565063833812852957431399329178076612672402875371133625034004959052613191487890835757740396589393492844874939153189578115961058990208616476352266475240786019670398731747632154724685625511852567184980938252519723945171239590160547146471407586102947610688
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
end Taeyoung.Methods.RootedSOS.Refinement.Atlas159.Target

namespace Taeyoung.Methods.RootedSOS.Refinement.Atlas159

/-- The target polynomial `Φ_H(p) = (1-p)^{v(H)} P_H(1/(1-p))` of Atlas 159. -/
noncomputable def target159 (p : Real) : Real :=
  (0)*p^0 + (0)*p^1 + (-3)*p^2 + (15)*p^3 + (-25)*p^4 + (14)*p^5 + (0)*p^6

end Taeyoung.Methods.RootedSOS.Refinement.Atlas159
