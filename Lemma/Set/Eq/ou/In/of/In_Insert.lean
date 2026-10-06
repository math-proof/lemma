import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {α : Type*}
  {e a b c : α}
-- given
  (h : e ∈ ({a, b, c} : Set α)) :
-- imply
  e = a ∨ e = b ∨ e = c := by
-- proof
  simpa using h


-- created on 2018-04-26
