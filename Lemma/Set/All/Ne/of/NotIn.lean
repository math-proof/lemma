import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {S : Set α}
  {e : α}
-- given
  (h : e ∉ S) :
-- imply
  ∀ x ∈ S, e ≠ x := by
-- proof
  intro x hx hxe
  subst hxe
  exact h hx


-- created on 2021-01-13
