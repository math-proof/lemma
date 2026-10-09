import sympy.Basic


@[path]
private lemma main
  [CommSemiring α]
  {n : ℕ}
  {x y : Fin n → α} :
-- imply
  ∑ i, y i * x i = y ⬝ᵥ x :=
-- proof
  rfl


-- created on 2020-11-18
-- updated on 2026-10-10
