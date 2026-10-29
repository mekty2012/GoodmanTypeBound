import Taeyoung.Methods.RootedSOS.Encoding

/-!
# Decoding bounded exact Gram witnesses

This is the certificate-independent theorem behind the row-local arithmetic
checks.  Positional equality plus explicit digit bounds recovers the exact
entries of `K = F (D I + C)` and `G = K Fᵀ`.
-/

open Finset
open scoped BigOperators

namespace Taeyoung.Methods.RootedSOS

def expectedIntermediate {m n : Nat} (denominator : Nat)
    (factor : Fin m → Fin n → Int) (correction : Fin n → Fin n → Int)
    (row : Fin m) (col : Fin n) : Int :=
  factor row col * denominator +
    ∑ i : Fin n, factor row i * correction i col

theorem expectedIntermediate_bound {m n : Nat}
    (denominator factorBound correctionBound intermediateBound : Nat)
    (factor : Fin m → Fin n → Int) (correction : Fin n → Fin n → Int)
    (hformula : intermediateBound =
      denominator * factorBound + n * factorBound * correctionBound)
    (hfactor : ∀ row col, (factor row col).natAbs ≤ factorBound)
    (hcorrection : ∀ i j, (correction i j).natAbs ≤ correctionBound)
    (row : Fin m) (col : Fin n) :
    (expectedIntermediate denominator factor correction row col).natAbs ≤
      intermediateBound := by
  have h := matrix_product_entry_bound denominator factorBound correctionBound
    (factor row col) (fun i => factor row i) (fun i => correction i col)
    (hfactor row col) (hfactor row) (fun i => hcorrection i col)
  rw [hformula]
  simpa [expectedIntermediate] using h

theorem intermediate_entries_exact {m n : Nat}
    (denominator factorBound correctionBound intermediateBound base : Nat)
    (factor : Fin m → Fin n → Int) (correction : Fin n → Fin n → Int)
    (intermediate : Fin m → Fin n → Int) (correctionEncoding : Fin n → Int)
    (hpositive : 0 < intermediateBound)
    (hbase : base = 2 * intermediateBound + 1)
    (hformula : intermediateBound =
      denominator * factorBound + n * factorBound * correctionBound)
    (hfactor : ∀ row col, (factor row col).natAbs ≤ factorBound)
    (hcorrection : ∀ i j, (correction i j).natAbs ≤ correctionBound)
    (hintermediate : ∀ row col,
      (intermediate row col).natAbs ≤ intermediateBound)
    (hcorrectionEncoding : ∀ i,
      correctionEncoding i =
        ∑ j : Fin n, correction i j * (base : Int) ^ j.1)
    (hintermediateEncoding : ∀ row,
      shiftedEncoding base intermediateBound
          (List.ofFn fun j : Fin n => intermediate row j) =
        intermediateBound * geometricEncoding base n +
          denominator *
            (∑ j : Fin n, factor row j * (base : Int) ^ j.1) +
          ∑ i : Fin n, factor row i * correctionEncoding i)
    (row : Fin m) (col : Fin n) :
    intermediate row col =
      expectedIntermediate denominator factor correction row col := by
  have hexpected := expectedIntermediate_bound denominator factorBound
    correctionBound intermediateBound factor correction hformula hfactor
    hcorrection row
  have hencoding :
      shiftedEncoding base intermediateBound
          (List.ofFn fun j : Fin n => intermediate row j) =
        shiftedEncoding base intermediateBound
          (List.ofFn fun j : Fin n =>
            expectedIntermediate denominator factor correction row j) := by
    rw [shiftedEncoding_ofFn_eq_sum _ hexpected]
    simp only [expectedIntermediate]
    rw [encoded_matrix_product base intermediateBound
      (fun j : Fin n => factor row j * denominator)
      (fun i : Fin n => factor row i) correction]
    simp_rw [← hcorrectionEncoding]
    rw [hintermediateEncoding]
    rw [Finset.mul_sum]
    ring_nf
    rw [show (∑ x : Fin n,
        (denominator : Int) * factor row x * (base : Int) ^ x.1) =
        ∑ x : Fin n,
          (denominator : Int) * (base : Int) ^ x.1 * factor row x by
      apply Finset.sum_congr rfl
      intro x _
      ring]
    abel
  have hfun := shiftedEncoding_injective_of_bound hpositive hbase
    (fun j : Fin n => intermediate row j)
    (fun j : Fin n => expectedIntermediate denominator factor correction row j)
    (hintermediate row) hexpected hencoding
  exact congrFun hfun col

end Taeyoung.Methods.RootedSOS
