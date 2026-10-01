import sympy.Basic


@[main]
private lemma main
  [Decidable p]
  {n : ℕ}
-- given
  (h : n > 0) :
-- imply
  Bool.toNat p = (Bool.toNat p) ^ n := by
-- proof
  cases n with
  | zero =>
    omega
  | succ k =>
    by_cases hp : p
    ·
      simp [hp]
    ·
      simp [hp]


-- created on 2019-03-06
