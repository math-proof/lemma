import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {x : Fin n → ℝ}
  {e : ℝ} :
-- imply
  (fun i => x i) ^ e = fun i => x i ^ e :=
-- proof
  rfl


-- created on 2026-09-27
