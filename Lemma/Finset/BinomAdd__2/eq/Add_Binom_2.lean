import sympy.Basic


@[main]
private lemma main
  {x y : ℕ} :
-- imply
  (x + y).choose 2 = y.choose 2 + x.choose 2 + y * x := by
-- proof
  rw [Nat.add_choose_eq]
  simp [Finset.Nat.antidiagonal_succ]
  ring


-- created on 2022-07-11
