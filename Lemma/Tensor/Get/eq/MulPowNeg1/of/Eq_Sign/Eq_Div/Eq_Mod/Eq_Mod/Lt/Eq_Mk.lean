import sympy.functions.elementary.integers
import sympy.Basic


@[main]
private lemma mxfp4
  -- {K : Type*} [Field K] {FP4_VALUES : List.Vector K 16}
  {FP4_VALUES : List.Vector ℝ 16}
  {n : ℕ}
-- given
  (h₀ : FP4_VALUES = ⟨[0.0, 0.5, 1.0, 1.5, 2.0, 3.0, 4.0, 6.0, -0.0, -0.5, -1.0, -1.5, -2.0, -3.0, -4.0, -6.0], rfl⟩)
  (h₁ : n < 16)
  -- Mantissa/significand
  (h₂ : M = n % 2)
  -- Exponent
  (h₃ : E = (n / 2) % 4)
  -- Sign
  (h₄ : S = n / 8)
  -- Exponent bias (or normalization adjustment)
  (h₅ : bias = sign E) :
-- imply
  FP4_VALUES[n] = (-1) ^ S * (2 ^ (E - bias)) * (M / 2 + bias) := by
-- proof
  rw [h₀, h₂, h₃, h₄, h₅, h₃]
  interval_cases n <;>
  ·
    norm_num [Int.sign]
    simp
    rfl


-- created on 2025-08-29
