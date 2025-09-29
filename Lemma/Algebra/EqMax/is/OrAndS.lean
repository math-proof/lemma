import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  [LinearOrder α]
-- given
  (a b c : α) :
-- imply
  a ⊔ b = c ↔ a = c ∧ b ≤ a ∨ b = c ∧ a ≤ b :=
-- proof
  max_eq_iff


-- created on 2025-08-02
