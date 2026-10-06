import sympy.Basic


@[main]
private lemma main
  {A B X : Set α}
-- given
  (h : A ⊆ B)
  (hx : X ⊆ A) :
-- imply
  X ⊆ B := by
-- proof
  exact hx.trans h


-- created on 2022-09-20
