import Mathlib
import sympy.Basic

open Polynomial

/--
[Polynomial_separable_sub_C_of_forall_eval_derivative](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Polynomial_separable_sub_C_of_forall_eval_derivative.lean)
-/
@[path]
private lemma main
  {k : Type u} [Field k] [IsAlgClosed k]
  {P : k[X]}
  {c : k}
-- given
  (hc : ∀ x : k, (derivative P).eval x = 0 → P.eval x ≠ c) :
-- imply
  (P - C c).Separable := by
-- proof
  rw [Polynomial.separable_def, derivative_sub, derivative_C, sub_zero,
    Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed k k]
  intro a
  by_cases h : (derivative P).eval a = 0
  · left
    rw [coe_aeval_eq_eval, eval_sub, eval_C]
    exact sub_ne_zero.mpr (hc a h)
  · right
    rwa [coe_aeval_eq_eval]


-- created on 2026-10-05
