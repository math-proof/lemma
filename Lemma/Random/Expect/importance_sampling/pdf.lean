import Mathlib.Algebra.BigOperators.Ring.Finset
import sympy.Basic
open Finset


/--
Finite importance sampling: reweighting by the likelihood ratio `μ / ν` preserves the expectation.
-/
@[path]
private lemma main
  [Fintype ι]
  {f μ ν : ι → ℝ}
-- given
  (h₀ : ∀ i, ν i ≠ 0) :
-- imply
  ∑ i, f i * μ i = ∑ i, f i * (μ i / ν i) * ν i := by
-- proof
  refine sum_congr rfl fun i _ => ?_
  field_simp [h₀ i]


-- created on 2023-03-25
-- updated on 2026-10-17
