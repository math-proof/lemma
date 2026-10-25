/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/Log/Integral.lean -/


import Def.Analysis.SpecialFunctions.Log.Integral
import Lemma.Real.Integral
open MeasureTheory


noncomputable section

namespace Real

example : LogarithmicIntegralDomain :=
  ⟨0, by constructor <;> norm_num⟩

example : LogarithmicIntegralDomain :=
  ⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩

example : LogarithmicIntegralDomain :=
  ⟨2, by constructor <;> norm_num⟩

example : ¬ ∃ x : LogarithmicIntegralDomain, x.val = 1 := by
  rintro ⟨x, hx⟩
  exact x.property.2 hx

example :
    logarithmicIntegral ⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩ =
      ∫ t in (0 : ℝ)..(1 : ℝ) / 2, (log t)⁻¹ := by
  apply logarithmicIntegral_of_lt_one
  norm_num

example :
    logarithmicIntegral ⟨(2 : ℝ), by constructor <;> norm_num⟩ =
      ∫ u in (0 : ℝ)..(1 : ℝ), ((log (1 - u))⁻¹ + (log (1 + u))⁻¹) := by
  rw [logarithmicIntegral_of_one_lt (by norm_num)]
  simp

end Real
end
