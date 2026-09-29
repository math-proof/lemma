import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {x : ℕ → Fin n → ℝ} :
-- imply
  (fun (i : Fin n) => ∑ j, x i j) = fun i : Fin n => ∑ j : Fin n, x i j :=
-- proof
  rfl


-- created on 2026-09-27
