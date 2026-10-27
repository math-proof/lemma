import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a : α}
  {A B : Set α}
-- given
  (_h : a ∈ A)
  (heq : B ∪ {a} = A) :
-- imply
  A \ {a} = B \ {a} := by
-- proof
  ext y
  rw [← heq]
  simp


-- created on 2021-04-05
-- updated on 2026-10-26
