import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {e : α}
  {A B C : Set α}
-- given
  (h : e ∈ A ∪ B ∪ C) :
-- imply
  e ∈ A ∨ e ∈ B ∨ e ∈ C := by
-- proof
  simpa [or_assoc] using h


-- created on 2018-04-25
