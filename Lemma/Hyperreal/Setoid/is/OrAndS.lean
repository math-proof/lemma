import sympy.sets.fancyset
import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
-- given
  (a b : ℝ*) :
-- imply
  a ≈ b ↔ (a → 0) ∧ b → 0 ∨ (a / b - 1) → 0 ∧ ¬b → 0:= by
-- proof
  rfl


-- created on 2025-12-08
