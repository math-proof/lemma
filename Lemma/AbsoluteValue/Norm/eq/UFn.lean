import Mathlib
import sympy.Basic


@[main]
private lemma main
-- given
  {K : Type*} [Field K]
  (v : AbsoluteValue K ℝ)
  (x : K) :
-- imply
  ‖(x : v.Completion)‖ = v x := by
-- proof
  rw [UniformSpace.Completion.norm_coe, WithAbs.norm_eq_apply_ofAbs]


-- created on 2026-09-19
