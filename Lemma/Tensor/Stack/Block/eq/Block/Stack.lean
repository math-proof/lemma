import sympy.Basic


@[path]
private lemma main
  {m p q : ℕ}
  {a : Fin m → Fin p → ℝ}
  {b : Fin m → Fin q → ℝ} :
-- imply
  (fun i => Fin.append (a i) (b i)) = fun i j => Fin.append (a i) (b i) j :=
-- proof
  rfl


-- created on 2021-12-30
