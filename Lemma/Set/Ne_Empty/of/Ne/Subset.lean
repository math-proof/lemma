import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {A B : Set α}
-- given
  (h : A ≠ B)
  (h₀ : A ⊆ B) :
-- imply
  B \ A ≠ ∅ := by
-- proof
  apply Set.nonempty_iff_ne_empty.mp
  apply Set.sdiff_nonempty.mpr
  intro hBA
  exact h (Set.Subset.antisymm h₀ hBA)


-- created on 2021-06-04
