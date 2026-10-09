import Mathlib
import sympy.Basic
import sympy.Analysis.Complex.WeierstrassFactorization

open Complex.WeierstrassFactorizationWanted

/-- [weierstrass_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/WeierstrassFactorization.lean) -/
@[path]
private lemma weierstrass_factorization_eq
-- given
  (S : Set ℂ)
  (hS_closed : IsClosed S)
  (hS_discrete : ∀ z ∈ S, ∃ ε > 0, (Metric.ball z ε \ {z}) ∩ S = ∅) :
-- imply
  ∃ f : ℂ → ℂ, Differentiable ℂ f ∧
    (∀ z : ℂ, f z = 0 ↔ z ∈ S) ∧
    (∀ z ∈ S, deriv f z ≠ 0) := by
-- proof
  apply weierstrass_factorization S hS_closed hS_discrete

-- created on 2026-10-10
