import Mathlib
import sympy.Basic
import sympy.calculus.LinearProgrammingDuality

open scoped Matrix

/--
[LinearProgrammingDuality](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Convex/LinearProgrammingDuality.lean)
-/
@[path]
private lemma strong_linear_programming_duality_eq
-- given
  {m n : ℕ}
  (A : Matrix (Fin m) (Fin n) ℝ)
  (b : Fin m → ℝ)
  (c : Fin n → ℝ)
  (hfeas : ∃ x : Fin n → ℝ, (∀ i, 0 ≤ x i) ∧ ∀ j, (A.mulVec x) j ≤ b j)
  (hbdd : ∃ M : ℝ, ∀ x : Fin n → ℝ,
    (∀ i, 0 ≤ x i) → (∀ j, (A.mulVec x) j ≤ b j) → c ⬝ᵥ x ≤ M) :
-- imply
  ∃ x : Fin n → ℝ, ∃ y : Fin m → ℝ,
    (∀ i, 0 ≤ x i) ∧ (∀ j, (A.mulVec x) j ≤ b j) ∧
    (∀ j, 0 ≤ y j) ∧ (∀ i, c i ≤ (A.transpose.mulVec y) i) ∧
    c ⬝ᵥ x = b ⬝ᵥ y := by
-- proof
  apply Convex.LPDuality.strong_linear_programming_duality A b c hfeas hbdd

-- created on 2026-10-10
