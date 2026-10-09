import sympy.Basic


@[path]
private lemma main
  [MonoidWithZero α]
  [NoZeroDivisors α]
  {x : α}
  {n : ℕ}
-- given
  (hn : 0 < n)
  (h : x ^ n = 0) :
-- imply
  x = 0 := by
-- proof
  exact (pow_eq_zero_iff (ne_of_gt hn)).mp h


-- created on 2018-11-03
