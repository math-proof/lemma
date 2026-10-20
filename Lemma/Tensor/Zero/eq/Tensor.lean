import sympy.Basic


@[path]
private lemma main
  {α : Type} [Zero α]
  {m n : ℕ} :
-- imply
  (0 : Matrix (Fin m) (Fin n) α) = Matrix.of fun _ _ => (0 : α) := by
-- proof
  ext i j
  simp


-- created on 2021-10-04
-- updated on 2026-10-17
