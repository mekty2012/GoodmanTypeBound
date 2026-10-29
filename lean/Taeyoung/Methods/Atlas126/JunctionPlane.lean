import Taeyoung.Methods.Atlas126.Junction
import Taeyoung.Methods.Atlas126.Plane
import Taeyoung.Methods.Atlas126.HighDegree
import Taeyoung.Methods.Atlas126.InteriorCutoff

/-! Assembly of the corrected junction plane from its four certificate
families. The zero parameter cases are included by a closed interval scaling
lemma, so no division-by-zero cases are delegated to generated certificates. -/

namespace Taeyoung.Methods.Atlas126

theorem exists_unit_scale {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) (hta : t ≤ a) :
    ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ a*u = t := by
  by_cases hz : a = 0
  · have ht0 : t = 0 := by linarith
    exact ⟨0, le_rfl, zero_le_one, by simp [hz, ht0]⟩
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
    refine ⟨t/a, div_nonneg ht ha, (div_le_one hapos).mpr hta, ?_⟩
    field_simp

end Taeyoung.Methods.Atlas126
