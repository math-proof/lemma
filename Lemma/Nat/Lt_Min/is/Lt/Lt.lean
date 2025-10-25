import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  [LinearOrder α]
-- given
  (x a b : α) :
-- imply
  x < a ⊓ b ↔ x < a ∧ x < b := by
-- proof
  constructor <;>
  ·
    intros
    simp_all


-- created on 2025-09-29
