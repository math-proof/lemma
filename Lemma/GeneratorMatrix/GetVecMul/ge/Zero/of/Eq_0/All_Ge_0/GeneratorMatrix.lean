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
  (h₁ : ∀ j, 0 ≤ x j)
  (h₂ : x i = 0) :
-- imply
  0 ≤ (x ᵥ* P) i := by
-- proof
  simp only [Matrix.vecMul, dotProduct]
  refine Finset.sum_nonneg fun j _ => ?_
  if h : j = i then
    subst h
    simp [h₂]
  else
    exact mul_nonneg (h₁ j) (h₀.offdiag_nonneg j i h)


-- created on 2026-09-26
