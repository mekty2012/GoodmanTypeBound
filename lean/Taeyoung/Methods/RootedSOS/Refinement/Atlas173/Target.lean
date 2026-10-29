import Taeyoung.Methods.RootedSOS.Induced.Six.Classification
import Taeyoung.Methods.RootedSOS.Induced.Six.Powers
import Taeyoung.Methods.RootedSOS.Induced.HomExpansion
import Taeyoung.Methods.RootedSOS.Induced.PatternCode
import Taeyoung.Methods.RootedSOS.Induced.Counts
import Taeyoung.Foundation.FiniteGraphEncoding

/-! Atlas 173: the homomorphism density on six sample points, expanded in the
156 induced densities, and the target polynomial `Φ_H`. -/

namespace Taeyoung.Methods.RootedSOS.Refinement.Atlas173.Target
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
open Finset MeasureTheory Taeyoung
open Taeyoung.Methods.RootedSOS.Induced Taeyoung.Methods.RootedSOS.Induced.Six
def graph : SimpleGraph (Fin 6) := graphFromEdges 6 [(0, 1), (0, 3), (0, 5), (1, 2), (2, 3), (2, 4), (2, 5), (3, 4), (4, 5)]
instance : DecidableRel graph.Adj := by unfold graph; infer_instance
def presentIndex : Fin 9 → Fin 15 := ![0, 2, 4, 5, 9, 10, 11, 12, 14]
def freeIndex : Fin 6 → Fin 15 := ![1, 3, 6, 7, 8, 13]
def edgeMap : Fin 9 ⊕ Fin 6 → Fin 15 := Sum.elim presentIndex freeIndex
def edgeInv : Fin 15 → Fin 9 ⊕ Fin 6 := ![Sum.inl 0, Sum.inr 0, Sum.inl 1, Sum.inr 1, Sum.inl 2, Sum.inl 3, Sum.inr 2, Sum.inr 3, Sum.inr 4, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inr 5, Sum.inl 8]
private theorem edge_left : ∀ e, edgeInv (edgeMap e) = e := by decide +kernel
private theorem edge_right : ∀ e, edgeMap (edgeInv e) = e := by decide +kernel
def edgeEquiv : Fin 9 ⊕ Fin 6 ≃ Fin 15 := ⟨edgeMap,edgeInv,edge_left,edge_right⟩
private theorem present_injective : Function.Injective
    (fun i : Fin 9 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
private theorem edges_exact : graph.edgeFinset = univ.image
    (fun i : Fin 9 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
def completion (a : Fin 64) : Fin 32768 :=
  patternCode edgeEquiv (Sum.elim (fun _ => 1) (finFunctionFinEquiv.symm a))
private def histogramData : PackedTable := (.leaf (359299119803994805840682435266848020724553436801381652461646431201636355415307856067870876303158423907552068113893796079612345036250102379592265356418174414014366530031944077089891547460936835686169097192651366548250659084038992368358941665312332563544333908429647135350660685304967957149277643473755089161127207603032119284499023504709359627860769515114023513656490857841594367161511084924008537925643151035383017765949330465490326928276076238193686570290157223273264040837663922723524124689170095422205990927384194516539108396257402690527168338095112665296464831586048422293582586696659295971038096711174194288693858946088891164024736921020926445758859241146231499286182206010025782536171161126092034643422386881094035027966435946382748387049536))
def histogram (b : Fin 1) : Int := histogramData.get b
def countCode : Nat := 11772974685805685739081614865951173883318873654508749972161363100674279479515389450265963478874167780913619906728899792515727795066938119192381636260709994244065674927866954222238345113358396211513464031744480624486367878237279633626826981354736867370754231510284620696138306956756430260639732954082632149511254122587801900839047688479877469066937473248203118733788327705364077544207739586491898282343339097117115468713486832973868531775138256366849613276625282214219370526968780025344639788020702209959159000562363688306648108734157177661174846771204958394927998643609174351299059838519838849144147204471040154314660433125082182872946085479615201280465802205607044688653498604841999118900307651016009806570904356256265530299704397561002233202016059456
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
end Taeyoung.Methods.RootedSOS.Refinement.Atlas173.Target

namespace Taeyoung.Methods.RootedSOS.Refinement.Atlas173

/-- The target polynomial `Φ_H(p) = (1-p)^{v(H)} P_H(1/(1-p))` of Atlas 173. -/
noncomputable def target173 (p : Real) : Real :=
  (0)*p^0 + (3)*p^1 + (-20)*p^2 + (50)*p^3 + (-56)*p^4 + (24)*p^5 + (0)*p^6

end Taeyoung.Methods.RootedSOS.Refinement.Atlas173
