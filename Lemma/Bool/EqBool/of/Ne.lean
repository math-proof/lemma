import sympy.Basic


@[path]
private lemma main
  [DecidableEq β]
  {f : α → β}
  {x : α}
  {y : β}
-- given
  (h : f x ≠ y) :
-- imply
  Bool.toNat (f x ≠ y) = 1 := by
-- proof
  simp [h]


-- created on 2020-02-05
