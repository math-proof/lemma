import sympy.Basic


@[main]
private lemma main
  [Coe α β]
  {x y : α}
-- given
  (h : x = y) :
-- imply
  (x : β) = (y : β) := by
-- proof
  rw [h]


@[main]
private lemma reverse.given
  {a b : α}
-- given
  (h : b = a) :
-- imply
  a = b :=
-- proof
  h.symm


@[main]
private lemma swap
  {F G : α → α → β}
-- given
  (h : ∀ x y, F x y = G x y) :
-- imply
  ∀ x y, F y x = G y x :=
-- proof
  fun x y => h y x


-- created on 2019-03-29
-- updated on 2026-09-27
