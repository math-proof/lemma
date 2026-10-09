import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {x a : ℝ} :
-- imply
  (fun i : Fin n => x ^ (a * (1 : Fin n → ℝ) i)) = fun i => (x * (1 : Fin n → ℝ) i) ^ a := by
-- proof
  funext i
  simp


-- created on 2021-12-19
