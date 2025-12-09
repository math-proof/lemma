import sympy.sets.fancyset
import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
-- given
  (a b : ℝ*) :
-- imply
  a ≈ b ↔ Infinitesimal a ∧ Infinitesimal b ∨ Infinitesimal (a / b - 1) ∧ ¬Infinitesimal b:= by
-- proof
  rfl


-- created on 2025-12-08
