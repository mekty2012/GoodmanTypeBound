import Taeyoung.Methods.RootedSOS.Refinement.Atlas158.High.ContractionChecks0000
import Taeyoung.Methods.RootedSOS.Refinement.Atlas158.High.ContractionChecks0052
import Taeyoung.Methods.RootedSOS.Refinement.Atlas158.High.ContractionChecks0104
namespace Taeyoung.Methods.RootedSOS.Refinement.Atlas158.High
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
theorem contractionCheck_all (k : Fin 156) : contractionCheck k := by
  by_cases h : k.1 < 52
  · let j : Fin 52 := ⟨k.1-0, by omega⟩
    have he : (⟨0+j.1, by omega⟩ : Fin 156) = k := by
      apply Fin.ext
      dsimp only [j]; omega
    simpa only [he] using ContractionChecks_0000 j
  by_cases h : k.1 < 104
  · let j : Fin 52 := ⟨k.1-52, by omega⟩
    have he : (⟨52+j.1, by omega⟩ : Fin 156) = k := by
      apply Fin.ext
      dsimp only [j]; omega
    simpa only [he] using ContractionChecks_0052 j
  by_cases h : k.1 < 156
  · let j : Fin 52 := ⟨k.1-104, by omega⟩
    have he : (⟨104+j.1, by omega⟩ : Fin 156) = k := by
      apply Fin.ext
      dsimp only [j]; omega
    simpa only [he] using ContractionChecks_0104 j
  omega

theorem groupTotal_exact (g : Fin 156) (u : Fin 3) :
    groupTotal g u = ∑ k : Fin 3632, Induced.Six.Sparse.pulled g k*right k u := by
  have h := packed_rect_product_exact
    (fun i j => Induced.Six.Sparse.pulled ⟨i%156,Nat.mod_lt _ (by decide)⟩ ⟨j%3632,Nat.mod_lt _ (by decide)⟩)
    right groupTotal 32768 756209333044298565295488000 89999025688310329807772464447488000 179998051376620659615544928894976001 rightEncoded
    (by
      intro i j
      exact decodeSignedDigit_bound (by decide) (Induced.Six.Sparse.flatCode _) _)
    (fun k u => ((rightCheck_all k).1 u).1)
    (fun g u => (contractionCheck_all g).1 u)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun k => (rightCheck_all k).2)
    (by
      intro g
      have hoff : (89999025688310329807772464447488000 : Int)*geometricEncoding 179998051376620659615544928894976001 3 = 2915905297928986287842565574876926307405132713048346417052804465274327091975384116240928235247542206464000 := by decide +kernel
      simp only [Nat.cast_ofNat, Nat.mod_eq_of_lt g.isLt, Nat.mod_eq_of_lt (Fin.isLt _)]
      rw [hoff, Induced.Six.Sparse.contraction]
      exact (contractionCheck_all g).2)
    g u
  simpa only [Nat.mod_eq_of_lt g.isLt, Nat.mod_eq_of_lt (Fin.isLt _)] using h
end Taeyoung.Methods.RootedSOS.Refinement.Atlas158.High
