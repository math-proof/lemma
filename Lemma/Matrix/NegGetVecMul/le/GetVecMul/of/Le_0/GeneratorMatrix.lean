import Mathlib.Algebra.Order.Group.PosPart
import sympy.stats.generator_matrix
import sympy.Basic
open Matrix


@[main]
private lemma main
  {S : Type*} [Fintype S]
  {P : Matrix S S ℝ}
  {x : S → ℝ}
  {i : S}
-- given
  (h₀ : GeneratorMatrix P)
  (h₁ : x i ≤ 0) :
-- imply
  -(x ᵥ* P) i ≤ (x⁻ ᵥ* P) i := by
-- proof
  have hx : ∀ j, x⁻ j = (x j)⁻ := fun j => rfl
  simp only [Matrix.vecMul, dotProduct, hx]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  if h : j = i then
    subst h
    rw [negPart_eq_neg.2 h₁, neg_mul]
  else
    have h2 : -x j ≤ (x j)⁻ := by
      rw [negPart_def]
      exact le_sup_left
    rw [← neg_mul]
    exact mul_le_mul_of_nonneg_right h2 (h₀.offdiag_nonneg j i h)


-- created on 2026-09-26
