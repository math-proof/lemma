import sympy.Basic


@[path]
private lemma main
  [AddCommMonoid α]
  {n : ℕ}
  {y : Fin n → Fin n → α} :
-- imply
  ∑ j : Fin n, ∑ i : Fin n, y j i = ∑ j : Fin n, ∑ i, (fun i => y j i) i :=
-- proof
  rfl


-- created on 2020-03-26
