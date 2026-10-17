import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {past : Fin n → ℝ}
  {a : ℝ} :
-- imply
  Sum.elim past (fun _ : Fin 1 => a) (Sum.inr 0) = a := by
-- proof
  simp


-- created on 2026-10-11
-- updated on 2026-10-17
