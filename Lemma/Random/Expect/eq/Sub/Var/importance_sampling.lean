import Mathlib.Algebra.BigOperators.Ring.Finset
import sympy.Basic
open Finset


/--
Finite importance-sampling variance gap. With likelihood ratio `λ = μ / ν`,
`∑ f² (1 - λ) μ = Var_μ(f) - Var_ν(f λ)`, where the squared means cancel because `∑ f λ ν = ∑ f μ`.
-/
@[path]
private lemma main
  [Fintype ι]
  {f μ ν : ι → ℝ}
-- given
  (h₀ : ∀ i, ν i ≠ 0) :
-- imply
  ∑ i, f i ^ 2 * (1 - μ i / ν i) * μ i =
    (∑ i, f i ^ 2 * μ i - (∑ i, f i * μ i) ^ 2) -
      (∑ i, (f i * (μ i / ν i)) ^ 2 * ν i - (∑ i, f i * (μ i / ν i) * ν i) ^ 2) := by
-- proof
  have hmean : ∑ i, f i * (μ i / ν i) * ν i = ∑ i, f i * μ i := by
    refine sum_congr rfl fun i _ => ?_
    field_simp [h₀ i]
  have hsq : ∑ i, (f i * (μ i / ν i)) ^ 2 * ν i = ∑ i, f i ^ 2 * (μ i / ν i) * μ i := by
    refine sum_congr rfl fun i _ => ?_
    field_simp [h₀ i]
  rw [hmean, hsq]
  have hlhs : ∑ i, f i ^ 2 * (1 - μ i / ν i) * μ i =
    ∑ i, f i ^ 2 * μ i - ∑ i, f i ^ 2 * (μ i / ν i) * μ i := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    field_simp [h₀ i]
  rw [hlhs]
  ring


-- created on 2023-03-24
-- updated on 2026-10-17
