import Taeyoung.Methods.RootedSOS.Induced.Six.Classification
import Taeyoung.Methods.RootedSOS.Induced.Six.Powers
import Taeyoung.Methods.RootedSOS.Induced.HomExpansion
import Taeyoung.Methods.RootedSOS.Induced.PatternCode
import Taeyoung.Methods.RootedSOS.Induced.Counts
import Taeyoung.Foundation.FiniteGraphEncoding

/-! Atlas 141: the homomorphism density on six sample points, expanded in the
156 induced densities, and the target polynomial `Φ_H`. -/

namespace Taeyoung.Methods.RootedSOS.Refinement.Atlas141.Target
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
open Finset MeasureTheory Taeyoung
open Taeyoung.Methods.RootedSOS.Induced Taeyoung.Methods.RootedSOS.Induced.Six
def graph : SimpleGraph (Fin 6) := graphFromEdges 6 [(0, 2), (1, 2), (1, 4), (2, 3), (2, 5), (3, 4), (3, 5), (4, 5)]
instance : DecidableRel graph.Adj := by unfold graph; infer_instance
def presentIndex : Fin 8 → Fin 15 := ![1, 5, 7, 9, 11, 12, 13, 14]
def freeIndex : Fin 7 → Fin 15 := ![0, 2, 3, 4, 6, 8, 10]
def edgeMap : Fin 8 ⊕ Fin 7 → Fin 15 := Sum.elim presentIndex freeIndex
def edgeInv : Fin 15 → Fin 8 ⊕ Fin 7 := ![Sum.inr 0, Sum.inl 0, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inl 1, Sum.inr 4, Sum.inl 2, Sum.inr 5, Sum.inl 3, Sum.inr 6, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7]
private theorem edge_left : ∀ e, edgeInv (edgeMap e) = e := by decide +kernel
private theorem edge_right : ∀ e, edgeMap (edgeInv e) = e := by decide +kernel
def edgeEquiv : Fin 8 ⊕ Fin 7 ≃ Fin 15 := ⟨edgeMap,edgeInv,edge_left,edge_right⟩
private theorem present_injective : Function.Injective
    (fun i : Fin 8 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
private theorem edges_exact : graph.edgeFinset = univ.image
    (fun i : Fin 8 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
def completion (a : Fin 128) : Fin 32768 :=
  patternCode edgeEquiv (Sum.elim (fun _ => 1) (finFunctionFinEquiv.symm a))
private def histogramData : PackedTable := (.leaf (359304601771587667064395985489678012607155556279064030412654689880120450344133826420329882022152566545903112578106496344594740267641369362525688515940536721011175169953942819471606793026477982479779312668360426043158381350618243343674530523179284468176129579943330483373963769208008558183383024500065408708670330957761036963550163774692243093279506726195177734172661507652082721236661097088361575603497267077656703142647333741115584636648151802240695624706217894988972575015213223831042813822621368937520662989785627332289453478098866520503505352885782781012310661002332425062017709545833495197162562029508516596472125067370970216647083120898605616290512540582984267906976264497217224815861290734004199668210280270876607582064223972459123672285312))
def histogram (b : Fin 1) : Int := histogramData.get b
def countCode : Nat := 11772974691287653331942838579501396713310756256628227654539314108932957963610318276236315937879886775056258257773364005215992777462169510459364569683869516606372671736506876220980726828603961752660257641959956333545862785959546212877802296943594734322658863305956134379486330259840333301240767059463658459830801665711156629756726739620147451950402891985414199888008843876013888032561814736504062635381016951233157742398863530977144157032846628442413660285679698274891086235502957574645747306709835661232674315234426089739463859079239019125004823108219749065043714489438590635301828273642688023343373328936358488636968211391203464951998707825815078959636333858906481441422119398900486310342587341145617718735929144149655312872258495349028309577301295232
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
end Taeyoung.Methods.RootedSOS.Refinement.Atlas141.Target

namespace Taeyoung.Methods.RootedSOS.Refinement.Atlas141

/-- The target polynomial `Φ_H(p) = (1-p)^{v(H)} P_H(1/(1-p))` of Atlas 141. -/
noncomputable def target141 (p : Real) : Real :=
  (0)*p^0 + (0)*p^1 + (-2)*p^2 + (10)*p^3 + (-17)*p^4 + (10)*p^5 + (0)*p^6

end Taeyoung.Methods.RootedSOS.Refinement.Atlas141
