import sympy.Basic


@[main]
private lemma main
  [Mul α]
  {n : ℕ}
  {f g : ℕ → α} :
-- imply
  (fun k : Fin n => f k) * (fun k : Fin n => g k) = fun k : Fin n => f k * g k :=
-- proof
  rfl


-- created on 2021-12-16
