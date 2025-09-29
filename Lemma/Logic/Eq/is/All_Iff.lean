import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
-- given
  (f g : α → Prop) :
-- imply
  f = g ↔ ∀ x, f x ↔ g x := by
-- proof
  constructor
  ·
    intro h x
    rw [h]
  ·
    intro h
    funext x
    specialize h x
    rw [h]


-- created on 2025-07-16
