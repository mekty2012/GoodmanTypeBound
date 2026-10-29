import Taeyoung.Methods.RootedSOS.Induced.Six.Classification
import Taeyoung.Methods.RootedSOS.Induced.Six.Powers
import Taeyoung.Methods.RootedSOS.Induced.HomExpansion
import Taeyoung.Methods.RootedSOS.Induced.PatternCode
import Taeyoung.Methods.RootedSOS.Induced.Counts
import Taeyoung.Foundation.FiniteGraphEncoding

/-! Atlas 190: the homomorphism density on six sample points, expanded in the
156 induced densities, and the target polynomial `Φ_H`. -/

namespace Taeyoung.Methods.RootedSOS.Refinement.Atlas190.Target
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
open Finset MeasureTheory Taeyoung
open Taeyoung.Methods.RootedSOS.Induced Taeyoung.Methods.RootedSOS.Induced.Six
def graph : SimpleGraph (Fin 6) := graphFromEdges 6 [(0, 1), (0, 2), (0, 5), (1, 2), (1, 3), (1, 4), (2, 5), (3, 4), (3, 5), (4, 5)]
instance : DecidableRel graph.Adj := by unfold graph; infer_instance
def presentIndex : Fin 10 → Fin 15 := ![0, 1, 4, 5, 6, 7, 11, 12, 13, 14]
def freeIndex : Fin 5 → Fin 15 := ![2, 3, 8, 9, 10]
def edgeMap : Fin 10 ⊕ Fin 5 → Fin 15 := Sum.elim presentIndex freeIndex
def edgeInv : Fin 15 → Fin 10 ⊕ Fin 5 := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inr 2, Sum.inr 3, Sum.inr 4, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9]
private theorem edge_left : ∀ e, edgeInv (edgeMap e) = e := by decide +kernel
private theorem edge_right : ∀ e, edgeMap (edgeInv e) = e := by decide +kernel
def edgeEquiv : Fin 10 ⊕ Fin 5 ≃ Fin 15 := ⟨edgeMap,edgeInv,edge_left,edge_right⟩
private theorem present_injective : Function.Injective
    (fun i : Fin 10 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
private theorem edges_exact : graph.edgeFinset = univ.image
    (fun i : Fin 10 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
def completion (a : Fin 32) : Fin 32768 :=
  patternCode edgeEquiv (Sum.elim (fun _ => 1) (finFunctionFinEquiv.symm a))
private def histogramData : PackedTable := (.leaf (359293637752758862891775526674890334228092972330402600806951591197263047519114876779935070396278775608533152970109736670217081344156671067909449808928753087610276505018897175352168071951004636588582404904803677236260356783500122526154853256712588487481007801366860972154235443571790880546741715224914790157861170840674436179921365561049407703660784884839776552456475367448956965342661922317580686133468774068969969528228908109660467720407023292062539228319712281755982980064392261538895436996799385932686249336664369012353024762489747994840156100686732867031738942160476699339092702410717009794172813658300063240526944512515058086363651303152253677406130545251572308466647928819129148370676734433491736783493838684565312658765133309708592866656288))
def histogram (b : Fin 1) : Int := histogramData.get b
def countCode : Nat := 11772974680323634503138665959042581925632377194044278993109708405834275106207493257286675543068260901265320887813756008456318399803246025761069953445162504822739270837841941175336607389882886279314366445052192776797055887934979094756984777266328267626678168184177557909975110531514697083563130418154383309212250856551039543155943110821933809115013273263572844486827127689873684906805920737329291854491546922740149055665249112551512701915930387313903482129283311769277853245908006753683455159333009839249669480820772968481143922650523410006479159758967550015129733917719748779576105348635552906857970339187987280183612266210648609039868424393997332607697449476911150029462679070564808222266142156589317206273044427708069001577335196258365559046495666208
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
end Taeyoung.Methods.RootedSOS.Refinement.Atlas190.Target

namespace Taeyoung.Methods.RootedSOS.Refinement.Atlas190

/-- The target polynomial `Φ_H(p) = (1-p)^{v(H)} P_H(1/(1-p))` of Atlas 190. -/
noncomputable def target190 (p : Real) : Real :=
  (0)*p^0 + (4)*p^1 + (-27)*p^2 + (68)*p^3 + (-76)*p^4 + (32)*p^5 + (0)*p^6

end Taeyoung.Methods.RootedSOS.Refinement.Atlas190
