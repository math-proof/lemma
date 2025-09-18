import sympy.concrete.quantifier
import Lemma.Basic


@[main, comm, mp, mpr]
private lemma main
-- given
  (f g p : α → Prop) :
-- imply
  (∃ x | f x, g x ∧ p x) ↔ ∃ x | f x ∧ g x, p x := by
-- proof
  aesop


@[main, comm, mp, mpr]
private lemma Comm
-- given
  (f g p : α → Prop) :
-- imply
  (∃ x | f x, p x ∧ g x) ↔ ∃ x | f x ∧ g x, p x := by
-- proof
  aesop


-- created on 2025-07-29
