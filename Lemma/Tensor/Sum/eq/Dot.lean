import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [CommSemiring α]
  {n : ℕ}
  {x y : Fin n → α} :
-- imply
  ∑ i, y i * x i = y ⬝ᵥ x :=
-- proof
  rfl


-- created on 2022-01-15
-- updated on 2026-10-26
