import Lemma.Basic


/--
This lemma establishes that in a group with zero `α` equipped with a partial order and satisfying `ZeroLEOneClass` and `PosMulReflectLT`, the inverse of an element `x` is positive if and only if `x` itself is positive.
It serves as a simplification rule to handle inequalities involving inverses in ordered algebraic structures.
-/
@[main, comm, mp, mpr]
private lemma main
  [GroupWithZero α]
  [PartialOrder α]
  [ZeroLEOneClass α]
  [PosMulReflectLT α]
  {x : α} :
-- imply
  x⁻¹ > 0 ↔ x > 0 :=
-- proof
  inv_pos


-- created on 2024-11-25
-- updated on 2025-04-04
