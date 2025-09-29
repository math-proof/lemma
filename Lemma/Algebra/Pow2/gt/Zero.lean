import sympy.Basic


@[main]
private lemma main
  {n : ℕ} :
-- imply
  2 ^ n > 0 := by
-- proof
  match n with
  | .zero =>
    simp
  | .succ n =>
    simp [Nat.pow_succ]


-- created on 2025-03-15
