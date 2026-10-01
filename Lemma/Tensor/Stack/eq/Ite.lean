import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {a j : ℤ}
  {g h : Fin n → ℤ → ℝ} :
-- imply
  (fun i => if j < a then g i j else h i j) = if j < a then (fun i => g i j) else fun i => h i j := by
-- proof
  split_ifs <;> rfl


-- created on 2019-10-19
