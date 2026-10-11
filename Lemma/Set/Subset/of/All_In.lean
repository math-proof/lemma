import sympy.Basic
open Set


@[path]
private lemma main
  {α} {A B : Set α}
-- given
  (h : B ⊆ A) :
-- imply
  ∀ x ∈ B, x ∈ A := by
-- proof
  intro x hx
  apply h hx


-- created on 2018-03-27
