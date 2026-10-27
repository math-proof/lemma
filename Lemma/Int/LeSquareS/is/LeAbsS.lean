import Theorem.Algebra.Power.Part2
import Initialize.Tactic.Attr.Basic


@[path, comm, mp, mpr]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
-- given
  (a b : α) :
-- imply
  a² ≤ b² ↔ |a| ≤ |b| :=
-- proof
  sq_le_sq


-- created on 2025-04-06
-- updated on 2026-10-26
