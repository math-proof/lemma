import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b : ℤ}
-- given
  (h₀ : Set.Ioo a b ≠ ∅) :
-- imply
  b > a :=
-- proof
  (Set.nonempty_iff_ne_empty.mpr h₀).elim fun _ hx => hx.1.trans hx.2


-- created on 2026-10-11
-- updated on 2026-10-17
