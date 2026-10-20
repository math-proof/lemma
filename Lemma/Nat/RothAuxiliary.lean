import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open scoped BigOperators
open scoped BigOperators nonZeroDivisors Polynomial
open MathlibExt.NumberTheory.RothAuxiliary


/--
[finite_of_divisible_approximations](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma finite_of_divisible_approximations_eq
  {α ε : ℝ}
  {S : Finset ι}
  {p : ι → ℕ}
  {μ ν : ι → ℝ}
-- given
  (hα : IsAlgebraic ℚ α)
  (hε : 0 < ε)
  (hεone : ε ≤ 1)
  (hμ : ∀ l ∈ S, 0 ≤ μ l)
  (hν : ∀ l ∈ S, 0 ≤ ν l)
  (hσ : ∑ l ∈ S, (μ l + ν l) < 2 + ε) :
-- imply
  Set.Finite {q : ℚ |
    |α - (q : ℝ)| <
    1 / Real.rpow (q.den : ℝ) (2 + ε - ∑ l ∈ S, (μ l + ν l)) ∧
    ∃ a b : ι → ℕ,
    ((∏ l ∈ S, p l ^ a l : ℕ) : ℤ) ∣ q.num ∧
    (∏ l ∈ S, p l ^ b l) ∣ q.den ∧
    ∀ l ∈ S,
    Real.rpow (q.den : ℝ) (μ l) ≤ (p l : ℝ) ^ a l ∧
    Real.rpow (q.den : ℝ) (ν l) ≤ (p l : ℝ) ^ b l} := by
-- proof
  apply MathlibExt.NumberTheory.RothAuxiliary.finite_of_divisible_approximations α hα ε hε hεone S p μ ν hμ hν hσ


-- created on 2026-10-20
