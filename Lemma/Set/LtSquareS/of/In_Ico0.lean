import sympy.sets.sets
import Lemma.Nat.Square.eq.Mul
open Nat


/--
If a real number `x` satisfies `0 ≤ x < b`, then its square is strictly less than `b²`.
This follows from the fact that squaring preserves the strict inequality for non-negative numbers.
-/
@[main]
private lemma main
  {x b : ℝ}
-- given
  (h₀ : x ∈ Ico 0 b) :
-- imply
  x² < b² := by
-- proof
  -- Extract the bounds from the interval `Ico 0 b`
  have ⟨h₁, h₂⟩ := h₀
  have := mul_self_lt_mul_self h₁ h₂
  repeat rw [Mul.eq.Square] at this
  assumption


-- created on 2025-03-24
-- updated on 2025-04-04
