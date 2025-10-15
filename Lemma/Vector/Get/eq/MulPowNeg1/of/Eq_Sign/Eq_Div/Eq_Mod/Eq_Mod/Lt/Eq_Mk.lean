import sympy.functions.elementary.integers
import sympy.Basic


/--
[MXFP4](https://arxiv.org/abs/2502.20586) is a data type used by [gpt-oss](https://huggingface.co/openai/gpt-oss-20b).
lemma applicable to :
  - ℚ ℝ ℝ* ℂ
-/
@[main]
private lemma mxfp4
  [Field R] [CharZero R]
  {FP4_VALUES : List.Vector R 16}
  {n : ℕ}
-- given
  -- explicit float definition of mxfp4
  (h₀ : FP4_VALUES = ⟨[0.0, 0.5, 1.0, 1.5, 2.0, 3.0, 4.0, 6.0, -0.0, -0.5, -1.0, -1.5, -2.0, -3.0, -4.0, -6.0], rfl⟩)
  (h₁ : n < 16)
  -- one bit for Mantissa/significand
  (h₂ : M = n &&& 1)
  -- two bits for Exponent
  (h₃ : E = n >>> 1 &&& 3)
  -- one bit for Sign
  (h₄ : S = n >>> 3)
  -- Exponent bias (or normalization adjustment)
  (h₅ : b = sign E) :
-- imply
  FP4_VALUES[n] = (-1) ^ S * 2 ^ (E - b) * (M / 2 + b) := by
-- proof
  rw [h₀, h₂, h₃, h₄, h₅, h₃]
  interval_cases n <;>
  ·
    norm_num [Int.sign]
    simp only [GetElem.getElem]
    simp [List.Vector.get]
    try norm_num


-- created on 2025-08-29
