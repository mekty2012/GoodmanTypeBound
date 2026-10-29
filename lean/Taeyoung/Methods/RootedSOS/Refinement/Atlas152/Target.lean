import Taeyoung.Methods.RootedSOS.Induced.Six.Classification
import Taeyoung.Methods.RootedSOS.Induced.Six.Powers
import Taeyoung.Methods.RootedSOS.Induced.HomExpansion
import Taeyoung.Methods.RootedSOS.Induced.PatternCode
import Taeyoung.Methods.RootedSOS.Induced.Counts
import Taeyoung.Foundation.FiniteGraphEncoding

/-! Atlas 152: the homomorphism density on six sample points, expanded in the
156 induced densities, and the target polynomial `Φ_H`. -/

namespace Taeyoung.Methods.RootedSOS.Refinement.Atlas152.Target
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
open Finset MeasureTheory Taeyoung
open Taeyoung.Methods.RootedSOS.Induced Taeyoung.Methods.RootedSOS.Induced.Six
def graph : SimpleGraph (Fin 6) := graphFromEdges 6 [(0, 1), (0, 5), (1, 2), (1, 5), (2, 3), (2, 4), (3, 4), (4, 5)]
instance : DecidableRel graph.Adj := by unfold graph; infer_instance
def presentIndex : Fin 8 → Fin 15 := ![0, 4, 5, 8, 9, 10, 12, 14]
def freeIndex : Fin 7 → Fin 15 := ![1, 2, 3, 6, 7, 11, 13]
def edgeMap : Fin 8 ⊕ Fin 7 → Fin 15 := Sum.elim presentIndex freeIndex
def edgeInv : Fin 15 → Fin 8 ⊕ Fin 7 := ![Sum.inl 0, Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inl 1, Sum.inl 2, Sum.inr 3, Sum.inr 4, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inr 5, Sum.inl 6, Sum.inr 6, Sum.inl 7]
private theorem edge_left : ∀ e, edgeInv (edgeMap e) = e := by decide +kernel
private theorem edge_right : ∀ e, edgeMap (edgeInv e) = e := by decide +kernel
def edgeEquiv : Fin 8 ⊕ Fin 7 ≃ Fin 15 := ⟨edgeMap,edgeInv,edge_left,edge_right⟩
private theorem present_injective : Function.Injective
    (fun i : Fin 8 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
private theorem edges_exact : graph.edgeFinset = univ.image
    (fun i : Fin 8 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
def completion (a : Fin 128) : Fin 32768 :=
  patternCode edgeEquiv (Sum.elim (fun _ => 1) (finFunctionFinEquiv.symm a))
private def histogramData : PackedTable := (.leaf (359304601938876383235385088812941632795154154827647486482865220086419618031115000167530605057693051686214039341163105257275557064788212024066151410415290280993552395637695937559762457421570750118156332364008181044679815836895965068118747504462633632813059378958688650965946279784026604067316549339881065971111634737685440332239150673773801125830747738257874432346970202384873255572372980351450750178250135285580912762481403477556958225111309564207568548684222137407321216148469650308794799206146754569625662491565719972574835975530979115905794953312133120574957021035611324086831607645689190149485748813629298267455066370473356593911986894625264784952816292183095922179894580677539009807357328711877047450204196287030922960471761714425904888348800))
def histogram (b : Fin 1) : Int := histogramData.get b
def countCode : Nat := 11772974691287820620659009568604719976930944255226776237995384319463164262778005257410063138602922315541398568700127061824905458278966657302026110146763991359932654113732559974098814984268356845427896018979651981300864307394032490599526741160576017671823500235755149737653922242350909319286650992988498275488064107014936554160095428607046533508435443226426262584707018184708620823096150448387325724555591704101365666608483365046880598406435091600175627158603676279133504584144090831072225058695219186618306420233927869832104144461736451237600225397820175415383277135798623914200853087540787879038325652123142609418639194332506567338375972729588805618804996162658081553076392317216666632127578837183595591583711138065671467187636902886770276358517358720
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
end Taeyoung.Methods.RootedSOS.Refinement.Atlas152.Target

namespace Taeyoung.Methods.RootedSOS.Refinement.Atlas152

/-- The target polynomial `Φ_H(p) = (1-p)^{v(H)} P_H(1/(1-p))` of Atlas 152. -/
noncomputable def target152 (p : Real) : Real :=
  (0)*p^0 + (1)*p^1 + (-7)*p^2 + (19)*p^3 + (-24)*p^4 + (12)*p^5 + (0)*p^6

end Taeyoung.Methods.RootedSOS.Refinement.Atlas152
