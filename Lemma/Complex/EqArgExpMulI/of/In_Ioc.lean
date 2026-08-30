import sympy.sets.sets
import sympy.Basic
import sympy.functions.elementary.complexes


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x ∈ Ioc (-π) π) :
-- imply
  arg ((I * x).exp) = x := by
-- proof
  rw [mul_comm I (x : ℂ), Complex.arg_exp_mul_I]
  refine (toIocMod_eq_self Real.two_pi_pos).mpr ⟨h.1, ?_⟩
  have : (-π + 2 * π : ℝ) = π := by ring
  grind


-- created on 2018-11-07
-- updated on 2026-08-20
