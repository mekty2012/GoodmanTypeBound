import Taeyoung.Methods.RootedSOS.Induced.Six.Classification
import Taeyoung.Methods.RootedSOS.Induced.Six.Powers
import Taeyoung.Methods.RootedSOS.Induced.HomExpansion
import Taeyoung.Methods.RootedSOS.Induced.PatternCode
import Taeyoung.Methods.RootedSOS.Induced.Counts
import Taeyoung.Foundation.FiniteGraphEncoding

/-! Atlas 182: the homomorphism density on six sample points, expanded in the
156 induced densities, and the target polynomial `Φ_H`. -/

namespace Taeyoung.Methods.RootedSOS.Refinement.Atlas182.Target
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
open Finset MeasureTheory Taeyoung
open Taeyoung.Methods.RootedSOS.Induced Taeyoung.Methods.RootedSOS.Induced.Six
def graph : SimpleGraph (Fin 6) := graphFromEdges 6 [(0, 2), (0, 3), (0, 5), (1, 2), (1, 3), (2, 3), (2, 4), (2, 5), (3, 4), (4, 5)]
instance : DecidableRel graph.Adj := by unfold graph; infer_instance
def presentIndex : Fin 10 → Fin 15 := ![1, 2, 4, 5, 6, 9, 10, 11, 12, 14]
def freeIndex : Fin 5 → Fin 15 := ![0, 3, 7, 8, 13]
def edgeMap : Fin 10 ⊕ Fin 5 → Fin 15 := Sum.elim presentIndex freeIndex
def edgeInv : Fin 15 → Fin 10 ⊕ Fin 5 := ![Sum.inr 0, Sum.inl 0, Sum.inl 1, Sum.inr 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inr 2, Sum.inr 3, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inr 4, Sum.inl 9]
private theorem edge_left : ∀ e, edgeInv (edgeMap e) = e := by decide +kernel
private theorem edge_right : ∀ e, edgeMap (edgeInv e) = e := by decide +kernel
def edgeEquiv : Fin 10 ⊕ Fin 5 ≃ Fin 15 := ⟨edgeMap,edgeInv,edge_left,edge_right⟩
private theorem present_injective : Function.Injective
    (fun i : Fin 10 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
private theorem edges_exact : graph.edgeFinset = univ.image
    (fun i : Fin 10 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
def completion (a : Fin 32) : Fin 32768 :=
  patternCode edgeEquiv (Sum.elim (fun _ => 1) (finFunctionFinEquiv.symm a))
private def histogramData : PackedTable := (.leaf (359293637585470146701312642253448074896673849332274019927902119088478712341435042505336220684109081408220362499940875601819285034082110871323875997000275788175961366317653341840985301830803503565232538473664885982022649551971638383369463994697747277905828337689013461633142704854755529888570980647487405081140094737012926378202298708579242363443730402631715119276028429597423010300957288142810680480599914507635999412679272090861539184093835135974924477090203513719099855955214298059747294744818981779035771558976106628127236709622434057813014332174980153769910814886675463617761835982669409738076203958399090670677635818077816226150940618143589043048950725965914031390071677529791745125394970178544257252808444173121627239433811689718006778822688))
def histogram (b : Fin 1) : Int := histogramData.get b
def countCode : Nat := 11772974680323467214422475496158160483373045774921280864528829356362166321872315577452400944218548731571120575023285839595250002006935951200873367871350576345439836522703239931503096207112766078181343095185761638005801650227747566272841991877066252785468593004713880062464589438775980048212472247419805881827174135474935881646141391755081338949673056209090636425393947242935833372850879032695117084485894053880587721695133562915493902987394074125747394514532082260509816362783897575719976011190757858845515830342995280218759696862470542692542132617199038262416472089592474978340384017769124859257914242578287379211042416901954171798008211683312323943063092297091864371185602494313518884862896874825062258793513742313557557891915864936745568460407832608
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
end Taeyoung.Methods.RootedSOS.Refinement.Atlas182.Target

namespace Taeyoung.Methods.RootedSOS.Refinement.Atlas182

/-- The target polynomial `Φ_H(p) = (1-p)^{v(H)} P_H(1/(1-p))` of Atlas 182. -/
noncomputable def target182 (p : Real) : Real :=
  (0)*p^0 + (3)*p^1 + (-21)*p^2 + (55)*p^3 + (-64)*p^4 + (28)*p^5 + (0)*p^6

end Taeyoung.Methods.RootedSOS.Refinement.Atlas182
