import sympy.sets.sets
import sympy.Basic
open Set


@[main]
private lemma main
  {α : Type*}
  {s : Set α}
  {p q : α → Prop}
-- given
  (h : ∀ x ∈ s, p x) :
-- imply
  ∀ x ∈ s, q x ∨ p x := by
-- proof
  intro x hx
  exact Or.inr (h x hx)


-- created on 2019-02-05
-- updated on 2023-05-20
