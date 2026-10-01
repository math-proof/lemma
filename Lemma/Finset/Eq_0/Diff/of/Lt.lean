import Mathlib.Algebra.Group.ForwardDiff
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n d : ℕ}
  {x : ℝ}
-- given
  (h : d < n) :
-- imply
  Nat.iterate (fwdDiff 1) n (fun x : ℝ => x ^ d) x = 0 := by
-- proof
  rw [fwdDiff_iter_pow_eq_zero_of_lt h, Pi.zero_apply]


-- created on 2021-12-01
