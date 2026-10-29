import Taeyoung.Methods.RootedSOS.Induced.Six.Classification
import Taeyoung.Methods.RootedSOS.Induced.Six.Powers
import Taeyoung.Methods.RootedSOS.Induced.HomExpansion
import Taeyoung.Methods.RootedSOS.Induced.PatternCode
import Taeyoung.Methods.RootedSOS.Induced.Counts
import Taeyoung.Foundation.FiniteGraphEncoding

/-! Atlas 140: the homomorphism density on six sample points, expanded in the
156 induced densities, and the target polynomial `Φ_H`. -/

namespace Taeyoung.Methods.RootedSOS.Refinement.Atlas140.Target
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
open Finset MeasureTheory Taeyoung
open Taeyoung.Methods.RootedSOS.Induced Taeyoung.Methods.RootedSOS.Induced.Six
def graph : SimpleGraph (Fin 6) := graphFromEdges 6 [(0, 1), (0, 2), (0, 3), (0, 4), (1, 3), (1, 5), (2, 3), (2, 5)]
instance : DecidableRel graph.Adj := by unfold graph; infer_instance
def presentIndex : Fin 8 → Fin 15 := ![0, 1, 2, 3, 6, 8, 9, 11]
def freeIndex : Fin 7 → Fin 15 := ![4, 5, 7, 10, 12, 13, 14]
def edgeMap : Fin 8 ⊕ Fin 7 → Fin 15 := Sum.elim presentIndex freeIndex
def edgeInv : Fin 15 → Fin 8 ⊕ Fin 7 := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inr 0, Sum.inr 1, Sum.inl 4, Sum.inr 2, Sum.inl 5, Sum.inl 6, Sum.inr 3, Sum.inl 7, Sum.inr 4, Sum.inr 5, Sum.inr 6]
private theorem edge_left : ∀ e, edgeInv (edgeMap e) = e := by decide +kernel
private theorem edge_right : ∀ e, edgeMap (edgeInv e) = e := by decide +kernel
def edgeEquiv : Fin 8 ⊕ Fin 7 ≃ Fin 15 := ⟨edgeMap,edgeInv,edge_left,edge_right⟩
private theorem present_injective : Function.Injective
    (fun i : Fin 8 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
private theorem edges_exact : graph.edgeFinset = univ.image
    (fun i : Fin 8 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
def completion (a : Fin 128) : Fin 32768 :=
  patternCode edgeEquiv (Sum.elim (fun _ => 1) (finFunctionFinEquiv.symm a))
private def histogramData : PackedTable := (.leaf (359304601771587667044921907227044559980921187368513724964576204668975894743805984067649639773897203131736319529883880061434705060840760774758292722636355781174750368341337969302864059274030184213892370740900791642650000588726787870073844309745044813559412461284366897749349209412198736650204683740752063560895873578380215672563537524627965832719542073028773130567524451984045490044151533844473144838286661417905643654844823612802623887139126235366379760131867045900400290964444569428231198206719874026380484779798915027452995364985580318688551377995279562625922213184912361106138097654992311933903946503528383600484093338927748268163440108568000292833397849865778402303845767793047529363298237078236235265229970772439052239077699703347748853514368))
def histogram (b : Fin 1) : Int := histogramData.get b
def countCode : Nat := 11772974691287653331942819105423134079858130022259317104233866030447746819054717948393963257637638519692844090980315782599709617426962709850776802288076212425432835311705263616130558085870209304861991755018028873911462277578784321422328696257381300083004246588837475415900705645280537491419233881122899146485653891253777248935435752993897387673142332020761033483405238738958219995330622226940818746950251740627497991339375728467015844072097119416846785969815123924041997663218906805991344495094219759737763175056216103027159022621125905838803008154244858561825328100990773215237872394030797182160110070320832508503972223359475021730050224182802748354312876744215764235556516268403782140647134778091961950771526163840156875316915508824759198202482524288
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
end Taeyoung.Methods.RootedSOS.Refinement.Atlas140.Target

namespace Taeyoung.Methods.RootedSOS.Refinement.Atlas140

/-- The target polynomial `Φ_H(p) = (1-p)^{v(H)} P_H(1/(1-p))` of Atlas 140. -/
noncomputable def target140 (p : Real) : Real :=
  (0)*p^0 + (0)*p^1 + (-2)*p^2 + (10)*p^3 + (-17)*p^4 + (10)*p^5 + (0)*p^6

end Taeyoung.Methods.RootedSOS.Refinement.Atlas140
