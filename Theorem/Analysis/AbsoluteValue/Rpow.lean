import Mathlib.Analysis.MeanInequalitiesPow
import Def.Analysis.AbsoluteValue.Rpow.Part2
/-!
# Real powers of absolute values

For `0 < c ≤ 1`, the function `x ↦ (v x) ^ c` is again an absolute value.
The triangle inequality follows from monotonicity and subadditivity of `Real.rpow`.
-/


noncomputable section

namespace AbsoluteValue

variable {R : Type*} [Semiring R]

/-- Evaluation of `AbsoluteValue.rpow`. -/
@[simp]
theorem rpow_apply (v : AbsoluteValue R ℝ) (c : ℝ) (hc₀ : 0 < c) (hc₁ : c ≤ 1) (x : R) :
    v.rpow c hc₀ hc₁ x = v x ^ c :=
  rfl

end AbsoluteValue
end
