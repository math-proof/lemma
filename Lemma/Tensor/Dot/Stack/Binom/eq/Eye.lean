import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {i j : ℕ} :
-- imply
  (Nat.choose i j) * j.factorial = i.descFactorial j ∧ (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 = 1 := by
-- proof
  constructor
  ·
    simpa [mul_comm] using (Nat.descFactorial_eq_factorial_mul_choose i j).symm
  ·
    simp


-- created on 2023-08-27
-- updated on 2026-10-26
