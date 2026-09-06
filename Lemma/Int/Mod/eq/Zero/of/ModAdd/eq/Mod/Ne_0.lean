import sympy.Basic


@[main]
private lemma main
  {x y d : ℤ}
-- given
  (_h_d : d ≠ 0)
  (h : (x + y) % d = x % d) :
-- imply
  y % d = 0 := by
-- proof
  rwa [Int.emod_eq_emod_iff_emod_sub_eq_zero, add_sub_cancel_left] at h


-- created on 2026-09-06
