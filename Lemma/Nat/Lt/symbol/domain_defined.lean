import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b : ℤ}
-- given
  (h₀ : Set.Ico a b ≠ ∅) :
-- imply
  a < b :=
-- proof
  (Set.nonempty_iff_ne_empty.mpr h₀).elim fun _ hx => lt_of_le_of_lt hx.1 hx.2


-- created on 2026-10-11
-- updated on 2026-10-17
