import sympy.Basic


@[main]
private lemma main
  {p q m n : ℕ}
  {y : Fin p → Fin q → Fin m → Fin n → ℝ} :
-- imply
  (fun a b c => ∑ j, y a b c j) = fun a b c => ∑ j : Fin n, y a b c j :=
-- proof
  rfl


-- created on 2026-09-27
