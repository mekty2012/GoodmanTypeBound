import Taeyoung.Methods.RootedSOS.Induced.Six.Classification
import Taeyoung.Methods.RootedSOS.Induced.Six.Powers
import Taeyoung.Methods.RootedSOS.Induced.HomExpansion
import Taeyoung.Methods.RootedSOS.Induced.PatternCode
import Taeyoung.Methods.RootedSOS.Induced.Counts
import Taeyoung.Foundation.FiniteGraphEncoding

/-! Atlas 48: the homomorphism density on six sample points, expanded in the
156 induced densities, and the target polynomial `Φ_H`. -/

namespace Taeyoung.Methods.RootedSOS.Refinement.Atlas48.Target
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
open Finset MeasureTheory Taeyoung
open Taeyoung.Methods.RootedSOS.Induced Taeyoung.Methods.RootedSOS.Induced.Six
def graph : SimpleGraph (Fin 6) := graphFromEdges 6 [(0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 4)]
instance : DecidableRel graph.Adj := by unfold graph; infer_instance
def presentIndex : Fin 7 → Fin 15 := ![1, 2, 3, 5, 6, 7, 10]
def freeIndex : Fin 8 → Fin 15 := ![0, 4, 8, 9, 11, 12, 13, 14]
def edgeMap : Fin 7 ⊕ Fin 8 → Fin 15 := Sum.elim presentIndex freeIndex
def edgeInv : Fin 15 → Fin 7 ⊕ Fin 8 := ![Sum.inr 0, Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 1, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inr 2, Sum.inr 3, Sum.inl 6, Sum.inr 4, Sum.inr 5, Sum.inr 6, Sum.inr 7]
private theorem edge_left : ∀ e, edgeInv (edgeMap e) = e := by decide +kernel
private theorem edge_right : ∀ e, edgeMap (edgeInv e) = e := by decide +kernel
def edgeEquiv : Fin 7 ⊕ Fin 8 ≃ Fin 15 := ⟨edgeMap,edgeInv,edge_left,edge_right⟩
private theorem present_injective : Function.Injective
    (fun i : Fin 7 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
private theorem edges_exact : graph.edgeFinset = univ.image
    (fun i : Fin 7 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
def completion (a : Fin 256) : Fin 32768 :=
  patternCode edgeEquiv (Sum.elim (fun _ => 1) (finFunctionFinEquiv.symm a))
private def histogramData : PackedTable := (.leaf (359310083822826162656009561904212563681903282394566391882817199023752879742414109934745372415291509947737985903271657077396857263104442978614791560324953604403090637762941104506018267100193850734505917925365500601571389717883096373446397346767270638805095448525872721553954934754647538763969697665224406165125682273266255342573051685007972036734280156210192185817180178213298261852416005623076071613092030541561728662469339263703693911285354709147641128871662281560962582089909835724429901773068104677129160844733378099431763624056611307817625181023150177151328686372219509624447315948641250589385382440723590283398117005763819048747685284113175711835719767080099109437728416590999365351684010054067268898402108183576828976888394212233324250792192))
def histogram (b : Fin 1) : Int := histogramData.get b
def countCode : Nat := 11772974696769704570438430193077811247861831004354343156900784271442101596039716556519830353370279913999660092646689170376725579579164973532980658786913901023256063651974685219265761240078035468528512368565213338620421198967913477730832068810418322308829492271824716921724510251005879940221347646136823618828258121062472134975105762508057767679346346758844214902460488394684449248102430491412597349877026545996621647424383352982666745142121265645320567231183863719277658225510032271257640693797786107968413923732281037490231001389384976869792137228047886432439853507463960522386390703249090831098765551756769703710655137383141857800830808427978293529731879066132978556263650151052580092483123163864937781805159335977568013093653319519268083777879802112
def coefficient (g : Fin 156) : Int := decodeSignedDigit 65537 32768 countCode g
private theorem count_total : (countCode : Int) = 11772615386685881744275774183515907035298149101071948590508901454243077843159974142409895607997864622489712354660785898719648182721901869090002043995353576069651660561336922278161255221810935274677777862647287973119819627578195594634458622413071555038190687176376191049002956296071125292682583676439158394422092995380198868719763189456372759707309612478688004710274671214506235949840578075406974273805413453966080085695720883643403041448209980290611419590054992056996097262927942361421916263896013039863736794571436304112131569625760920258484319602866863282262702178777588302876766255933142189848176166374328980120371739266136093981782060742694180354020043346365898457154212422635989093117771479854883714536260933869384436264676431125055850453629009920 + ∑ b, histogram b := by decide +kernel
private theorem block_000 : histogram 0 =
    ∑ i : Fin 256, groupPower (host (completion (finProdFinEquiv ((0 : Fin 1),i)))) := by decide +kernel
theorem histogram_exact (b : Fin 1) : histogram b =
    ∑ i : Fin 256, groupPower (host (completion (finProdFinEquiv (b,i)))) := by
  fin_cases b
  · exact block_000

theorem countCode_exact : (countCode : Int) = (32768 : Int)*geometricEncoding 65537 156 +
    ∑ a : Fin 256, (65537 : Int)^(host (completion a)).1 := by
  rw [histogram_offset]
  rw [← (finProdFinEquiv : Fin 1 × Fin 256 ≃ Fin 256).sum_comp
    (fun a : Fin 256 => (65537 : Int)^(host (completion a)).1)]
  simp only [Fintype.sum_prod_type]
  simp_rw [← groupPower_exact, ← histogram_exact]
  exact count_total
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
theorem hom_expansion (W : Graphon Ω μ) : homDensity graph W =
    ∑ a : Fin 256, density (host (completion a)) W := by
  rw [homDensity_completions graph pairs edgeEquiv present_injective edges_exact W]
  rw [← finFunctionFinEquiv.symm.sum_comp (fun q : Fin 8 → Fin 2 =>
    inducedDensity pairs (fun i => Sum.elim (fun _ => 1) q (edgeEquiv.symm i)) W)]
  apply Finset.sum_congr rfl
  intro a _
  have h := inducedDensity_classification (completion a) W
  simpa only [completion, patternCode, bits, Equiv.symm_apply_apply] using h
theorem density_expansion (W : Graphon Ω μ) : homDensity graph W =
    ∑ g : Fin 156, (coefficient g : Real)*density g W := by
  rw [hom_expansion]
  exact count_density_sum (fun a : Fin 256 => host (completion a))
    (by decide) (by norm_num) countCode_exact (fun g => density g W)
#print axioms density_expansion
end Taeyoung.Methods.RootedSOS.Refinement.Atlas48.Target

namespace Taeyoung.Methods.RootedSOS.Refinement.Atlas48

/-- The target polynomial `Φ_H(p) = (1-p)^{v(H)} P_H(1/(1-p))` of Atlas 48. -/
noncomputable def target48 (p : Real) : Real :=
  (0)*p^0 + (-2)*p^1 + (10)*p^2 + (-17)*p^3 + (10)*p^4 + (0)*p^5

end Taeyoung.Methods.RootedSOS.Refinement.Atlas48
