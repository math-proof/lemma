import sympy.Basic


@[main]
private lemma main
  [Add α]
  {n : ℕ}
  {j : Fin n}
  {x y : Fin n → Fin n → α} :
-- imply
  (fun i => x j i + y i j) = (fun i => x j i) + (fun i => y i j) :=
-- proof
  rfl


-- created on 2019-10-13
