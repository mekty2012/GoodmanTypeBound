import Taeyoung.Methods.RootedSOS.Induced.Six.Classification
import Taeyoung.Methods.RootedSOS.Induced.Six.Powers
import Taeyoung.Methods.RootedSOS.Induced.HomExpansion
import Taeyoung.Methods.RootedSOS.Induced.PatternCode
import Taeyoung.Methods.RootedSOS.Induced.Counts
import Taeyoung.Foundation.FiniteGraphEncoding

/-! Atlas 172: the homomorphism density on six sample points, expanded in the
156 induced densities, and the target polynomial `Φ_H`. -/

namespace Taeyoung.Methods.RootedSOS.Refinement.Atlas172.Target
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
open Finset MeasureTheory Taeyoung
open Taeyoung.Methods.RootedSOS.Induced Taeyoung.Methods.RootedSOS.Induced.Six
def graph : SimpleGraph (Fin 6) := graphFromEdges 6 [(0, 1), (0, 3), (0, 4), (0, 5), (1, 2), (1, 5), (2, 3), (2, 5), (3, 4)]
instance : DecidableRel graph.Adj := by unfold graph; infer_instance
def presentIndex : Fin 9 → Fin 15 := ![0, 2, 3, 4, 5, 8, 9, 11, 12]
def freeIndex : Fin 6 → Fin 15 := ![1, 6, 7, 10, 13, 14]
def edgeMap : Fin 9 ⊕ Fin 6 → Fin 15 := Sum.elim presentIndex freeIndex
def edgeInv : Fin 15 → Fin 9 ⊕ Fin 6 := ![Sum.inl 0, Sum.inr 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inr 1, Sum.inr 2, Sum.inl 5, Sum.inl 6, Sum.inr 3, Sum.inl 7, Sum.inl 8, Sum.inr 4, Sum.inr 5]
private theorem edge_left : ∀ e, edgeInv (edgeMap e) = e := by decide +kernel
private theorem edge_right : ∀ e, edgeMap (edgeInv e) = e := by decide +kernel
def edgeEquiv : Fin 9 ⊕ Fin 6 ≃ Fin 15 := ⟨edgeMap,edgeInv,edge_left,edge_right⟩
private theorem present_injective : Function.Injective
    (fun i : Fin 9 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
private theorem edges_exact : graph.edgeFinset = univ.image
    (fun i : Fin 9 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
def completion (a : Fin 64) : Fin 32768 :=
  patternCode edgeEquiv (Sum.elim (fun _ => 1) (finFunctionFinEquiv.symm a))
private def histogramData : PackedTable := (.leaf (359299119803994805860156216383163170202144653989740930844041492418345296712599011562302889986296064282648136218109789103447087495617140572926375990461666681795526476635021077104646901385513627880991847030954603386773605938466724252517953063110519853305984830434086412682663650022070458940240232830543613044490954538732180764773881030565475572512360191506144932168590323699962116427342211800573779921716500082893125876385226925266408036429854718034843578381840715204949740313656231646664631807918669524205726091906199648681442270224579287717939349790843137161945039686548504680237912741119953472675112932209670934483568688913821707738743976304606346333917728685479730872708649639744919050818925218634322347068438273408798613550041446648206182187072))
def histogram (b : Fin 1) : Int := histogramData.get b
def countCode : Nat := 11772974685805685739081634339732290198468351245725938331439745495735496188456686741421457910887850918553995002797004008508751629809397486230574970371344037736333456087813557299238359868712320788305658854494318927723206401184134061358711140366134665558043993161206625135415638959721147363141523916671988938035137486334737600900527963337403325182882124838879510855206839804829935911957005417618774847585335170466162978821597268870328307856246410145329454433633373897711302212668256017653562928527820958533261000297528210311780251068031144837772037542216654125399864123817274851381446493845883309801648841487261189791306222834825007803489799486670484960366377264094583936885085131285628838036822298780102348858608002307657845063289981166502498659811196992
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
end Taeyoung.Methods.RootedSOS.Refinement.Atlas172.Target

namespace Taeyoung.Methods.RootedSOS.Refinement.Atlas172

/-- The target polynomial `Φ_H(p) = (1-p)^{v(H)} P_H(1/(1-p))` of Atlas 172. -/
noncomputable def target172 (p : Real) : Real :=
  (0)*p^0 + (2)*p^1 + (-14)*p^2 + (37)*p^3 + (-44)*p^4 + (20)*p^5 + (0)*p^6

end Taeyoung.Methods.RootedSOS.Refinement.Atlas172
