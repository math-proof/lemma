import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {f : α → β}
  {p : α → Prop}
  {y : α}
-- given
  (h : f '' {x | p x} = {f y}) :
-- imply
  {x | p x} ≠ ∅ := by
-- proof
  apply Set.nonempty_iff_ne_empty.mp
  apply Set.image_nonempty.mp
  exact h.symm ▸ Set.singleton_nonempty (f y)


-- created on 2021-04-05
