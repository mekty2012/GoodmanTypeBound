import Taeyoung.Methods.RootedSOS.Induced.Six.Classification
import Taeyoung.Methods.RootedSOS.Induced.Six.Powers
import Taeyoung.Methods.RootedSOS.Induced.HomExpansion
import Taeyoung.Methods.RootedSOS.Induced.PatternCode
import Taeyoung.Methods.RootedSOS.Induced.Counts
import Taeyoung.Foundation.FiniteGraphEncoding

/-! Atlas 206: the homomorphism density on six sample points, expanded in the
156 induced densities, and the target polynomial `Φ_H`. -/

namespace Taeyoung.Methods.RootedSOS.Refinement.Atlas206.Target
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
open Finset MeasureTheory Taeyoung
open Taeyoung.Methods.RootedSOS.Induced Taeyoung.Methods.RootedSOS.Induced.Six
def graph : SimpleGraph (Fin 6) := graphFromEdges 6 [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 5), (2, 3), (2, 4), (3, 4), (3, 5), (4, 5)]
instance : DecidableRel graph.Adj := by unfold graph; infer_instance
def presentIndex : Fin 13 → Fin 15 := ![0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 13, 14]
def freeIndex : Fin 2 → Fin 15 := ![7, 11]
def edgeMap : Fin 13 ⊕ Fin 2 → Fin 15 := Sum.elim presentIndex freeIndex
def edgeInv : Fin 15 → Fin 13 ⊕ Fin 2 := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inr 0, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inr 1, Sum.inl 10, Sum.inl 11, Sum.inl 12]
private theorem edge_left : ∀ e, edgeInv (edgeMap e) = e := by decide +kernel
private theorem edge_right : ∀ e, edgeMap (edgeInv e) = e := by decide +kernel
def edgeEquiv : Fin 13 ⊕ Fin 2 ≃ Fin 15 := ⟨edgeMap,edgeInv,edge_left,edge_right⟩
private theorem present_injective : Function.Injective
    (fun i : Fin 13 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
private theorem edges_exact : graph.edgeFinset = univ.image
    (fun i : Fin 13 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
def completion (a : Fin 4) : Fin 32768 :=
  patternCode edgeEquiv (Sum.elim (fun _ => 1) (finFunctionFinEquiv.symm a))
private def histogramData : PackedTable := (.leaf (359277191682703049893141027945359336457096355934808298547191439087893665361161158098876707531260239681332821193272203598582484496880655416552927511527757154383662497588456122574335545745082167289899464855232306063020150843645140865744237251627201581143498501010397856696303619687797460542876922551981713722636937412777194298408234996608989435809427356200896730997365181865593202772757505545692865536340269965713914246260503128258381956426011854521182788235072795114307500913883309785984650769428457172531470724037609631836762028211927852134944545273067716133080143624192380209626217694054171425715701990388792324092299816888163188780972352816105915451380399276625966778319298096112037603217554298428538779894775278701047291385580031232109263192068))
def histogram (b : Fin 1) : Int := histogramData.get b
def countCode : Nat := 11772974663877564447325667324543852394634606197427883398807448645682165736825335303567994484705395882729393687481979170923246765206398749745418596922865103826806044223834510734283829557356680356845067762112143205425882647729039239775324366650323182239771830674877201446859652599690813090143126553361710376135815632317611645914061597691369368696745421906044205607005668579688101543043350832912519966670949794236045799609967144146531299830166406302465940772843227129791211570428856244731702248546782468320909326042160341721763406387789132186336454547412136349978835258921212495256975882150836244019601882076319368912695831565952982144970841715046996459935494726765175083120990741934085205155374697409182143075040828644663137311967816705087082562892201988
def coefficient (g : Fin 156) : Int := decodeSignedDigit 65537 32768 countCode g
private theorem count_total : (countCode : Int) = 11772615386685881744275774183515907035298149101071948590508901454243077843159974142409895607997864622489712354660785898719648182721901869090002043995353576069651660561336922278161255221810935274677777862647287973119819627578195594634458622413071555038190687176376191049002956296071125292682583676439158394422092995380198868719763189456372759707309612478688004710274671214506235949840578075406974273805413453966080085695720883643403041448209980290611419590054992056996097262927942361421916263896013039863736794571436304112131569625760920258484319602866863282262702178777588302876766255933142189848176166374328980120371739266136093981782060742694180354020043346365898457154212422635989093117771479854883714536260933869384436264676431125055850453629009920 + ∑ b, histogram b := by decide +kernel
private theorem block_000 : histogram 0 =
    ∑ i : Fin 4, groupPower (host (completion (finProdFinEquiv ((0 : Fin 1),i)))) := by decide +kernel
theorem histogram_exact (b : Fin 1) : histogram b =
    ∑ i : Fin 4, groupPower (host (completion (finProdFinEquiv (b,i)))) := by
  fin_cases b
  · exact block_000

theorem countCode_exact : (countCode : Int) = (32768 : Int)*geometricEncoding 65537 156 +
    ∑ a : Fin 4, (65537 : Int)^(host (completion a)).1 := by
  rw [histogram_offset]
  rw [← (finProdFinEquiv : Fin 1 × Fin 4 ≃ Fin 4).sum_comp
    (fun a : Fin 4 => (65537 : Int)^(host (completion a)).1)]
  simp only [Fintype.sum_prod_type]
  simp_rw [← groupPower_exact, ← histogram_exact]
  exact count_total
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
theorem hom_expansion (W : Graphon Ω μ) : homDensity graph W =
    ∑ a : Fin 4, density (host (completion a)) W := by
  rw [homDensity_completions graph pairs edgeEquiv present_injective edges_exact W]
  rw [← finFunctionFinEquiv.symm.sum_comp (fun q : Fin 2 → Fin 2 =>
    inducedDensity pairs (fun i => Sum.elim (fun _ => 1) q (edgeEquiv.symm i)) W)]
  apply Finset.sum_congr rfl
  intro a _
  have h := inducedDensity_classification (completion a) W
  simpa only [completion, patternCode, bits, Equiv.symm_apply_apply] using h
theorem density_expansion (W : Graphon Ω μ) : homDensity graph W =
    ∑ g : Fin 156, (coefficient g : Real)*density g W := by
  rw [hom_expansion]
  exact count_density_sum (fun a : Fin 4 => host (completion a))
    (by decide) (by norm_num) countCode_exact (fun g => density g W)
#print axioms density_expansion
end Taeyoung.Methods.RootedSOS.Refinement.Atlas206.Target

namespace Taeyoung.Methods.RootedSOS.Refinement.Atlas206

/-- The target polynomial `Φ_H(p) = (1-p)^{v(H)} P_H(1/(1-p))` of Atlas 206. -/
noncomputable def target206 (p : Real) : Real :=
  (0)*p^0 + (14)*p^1 + (-87)*p^2 + (201)*p^3 + (-205)*p^4 + (78)*p^5 + (0)*p^6

end Taeyoung.Methods.RootedSOS.Refinement.Atlas206
