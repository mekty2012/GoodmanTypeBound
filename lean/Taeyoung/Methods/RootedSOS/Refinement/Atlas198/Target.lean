import Taeyoung.Methods.RootedSOS.Induced.Six.Classification
import Taeyoung.Methods.RootedSOS.Induced.Six.Powers
import Taeyoung.Methods.RootedSOS.Induced.HomExpansion
import Taeyoung.Methods.RootedSOS.Induced.PatternCode
import Taeyoung.Methods.RootedSOS.Induced.Counts
import Taeyoung.Foundation.FiniteGraphEncoding

/-! Atlas 198: the homomorphism density on six sample points, expanded in the
156 induced densities, and the target polynomial `Φ_H`. -/

namespace Taeyoung.Methods.RootedSOS.Refinement.Atlas198.Target
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
open Finset MeasureTheory Taeyoung
open Taeyoung.Methods.RootedSOS.Induced Taeyoung.Methods.RootedSOS.Induced.Six
def graph : SimpleGraph (Fin 6) := graphFromEdges 6 [(0, 1), (0, 2), (0, 4), (0, 5), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 4), (3, 5)]
instance : DecidableRel graph.Adj := by unfold graph; infer_instance
def presentIndex : Fin 11 → Fin 15 := ![0, 1, 3, 4, 7, 8, 9, 10, 11, 12, 13]
def freeIndex : Fin 4 → Fin 15 := ![2, 5, 6, 14]
def edgeMap : Fin 11 ⊕ Fin 4 → Fin 15 := Sum.elim presentIndex freeIndex
def edgeInv : Fin 15 → Fin 11 ⊕ Fin 4 := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inl 2, Sum.inl 3, Sum.inr 1, Sum.inr 2, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inr 3]
private theorem edge_left : ∀ e, edgeInv (edgeMap e) = e := by decide +kernel
private theorem edge_right : ∀ e, edgeMap (edgeInv e) = e := by decide +kernel
def edgeEquiv : Fin 11 ⊕ Fin 4 ≃ Fin 15 := ⟨edgeMap,edgeInv,edge_left,edge_right⟩
private theorem present_injective : Function.Injective
    (fun i : Fin 11 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
private theorem edges_exact : graph.edgeFinset = univ.image
    (fun i : Fin 11 => s((pairs (edgeEquiv (.inl i))).1,(pairs (edgeEquiv (.inl i))).2)) := by decide +kernel
def completion (a : Fin 16) : Fin 32768 :=
  patternCode edgeEquiv (Sum.elim (fun _ => 1) (finFunctionFinEquiv.symm a))
private def histogramData : PackedTable := (.leaf (359288155701524196215537202059381949672414544342958399478710809947556039986545487985606267374126601120908729414702744721445237277950331498224866639485359066207529091218027704288751123327139036999296300805706373214975301282912986804243636961067322790638973145761618915948864480766268854077117242739697807776329210174930761091069839380689146506553483710557981787075890224198611087772220582757367495502181640121233671713160995844150695852645142797955035093045466609841898100028479320219405786163306108158118217706137167313082049826123876763844929751484866855274398601700880838120222735590166586681605887323432750041221295017531101153248159303261584893418951709020607906793541000825119807756910285053426481290588440683566734839473379019721233743740944))
def histogram (b : Fin 1) : Int := histogramData.get b
def countCode : Nat := 11772974674841583268471989720717966417247821515616291548908380165053025399199960687897881214265238749090833263390200601464369627959179819421500268861993061428717868090428140305865543972934262413714777158948093679493034602879478507621262866050032622360981326149521952667918905160551891561536660793681898092229869324590373799480854259295753448853816165962398562692061747104730434560928350295989731641300915635606201319367434044639247192144062625433409374625148037523605939161027970840742135669682176345971894912789142441279444651675587044135248164532618348149117976577379289183714886478668732356434857772261652412870412960561153625082935308901997441938913462298074919065061005963636814212925528390139937141017551522310068002999515904504075571687372750864
def coefficient (g : Fin 156) : Int := decodeSignedDigit 65537 32768 countCode g
private theorem count_total : (countCode : Int) = 11772615386685881744275774183515907035298149101071948590508901454243077843159974142409895607997864622489712354660785898719648182721901869090002043995353576069651660561336922278161255221810935274677777862647287973119819627578195594634458622413071555038190687176376191049002956296071125292682583676439158394422092995380198868719763189456372759707309612478688004710274671214506235949840578075406974273805413453966080085695720883643403041448209980290611419590054992056996097262927942361421916263896013039863736794571436304112131569625760920258484319602866863282262702178777588302876766255933142189848176166374328980120371739266136093981782060742694180354020043346365898457154212422635989093117771479854883714536260933869384436264676431125055850453629009920 + ∑ b, histogram b := by decide +kernel
private theorem block_000 : histogram 0 =
    ∑ i : Fin 16, groupPower (host (completion (finProdFinEquiv ((0 : Fin 1),i)))) := by decide +kernel
theorem histogram_exact (b : Fin 1) : histogram b =
    ∑ i : Fin 16, groupPower (host (completion (finProdFinEquiv (b,i)))) := by
  fin_cases b
  · exact block_000

theorem countCode_exact : (countCode : Int) = (32768 : Int)*geometricEncoding 65537 156 +
    ∑ a : Fin 16, (65537 : Int)^(host (completion a)).1 := by
  rw [histogram_offset]
  rw [← (finProdFinEquiv : Fin 1 × Fin 16 ≃ Fin 16).sum_comp
    (fun a : Fin 16 => (65537 : Int)^(host (completion a)).1)]
  simp only [Fintype.sum_prod_type]
  simp_rw [← groupPower_exact, ← histogram_exact]
  exact count_total
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
theorem hom_expansion (W : Graphon Ω μ) : homDensity graph W =
    ∑ a : Fin 16, density (host (completion a)) W := by
  rw [homDensity_completions graph pairs edgeEquiv present_injective edges_exact W]
  rw [← finFunctionFinEquiv.symm.sum_comp (fun q : Fin 4 → Fin 2 =>
    inducedDensity pairs (fun i => Sum.elim (fun _ => 1) q (edgeEquiv.symm i)) W)]
  apply Finset.sum_congr rfl
  intro a _
  have h := inducedDensity_classification (completion a) W
  simpa only [completion, patternCode, bits, Equiv.symm_apply_apply] using h
theorem density_expansion (W : Graphon Ω μ) : homDensity graph W =
    ∑ g : Fin 156, (coefficient g : Real)*density g W := by
  rw [hom_expansion]
  exact count_density_sum (fun a : Fin 16 => host (completion a))
    (by decide) (by norm_num) countCode_exact (fun g => density g W)
#print axioms density_expansion
end Taeyoung.Methods.RootedSOS.Refinement.Atlas198.Target

namespace Taeyoung.Methods.RootedSOS.Refinement.Atlas198

/-- The target polynomial `Φ_H(p) = (1-p)^{v(H)} P_H(1/(1-p))` of Atlas 198. -/
noncomputable def target198 (p : Real) : Real :=
  (0)*p^0 + (7)*p^1 + (-45)*p^2 + (108)*p^3 + (-115)*p^4 + (46)*p^5 + (0)*p^6

end Taeyoung.Methods.RootedSOS.Refinement.Atlas198
