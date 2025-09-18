import sympy.concrete.quantifier
import Lemma.Basic


@[main, comm, mp, mpr]
private lemma main
-- given
  (f p q : α → Prop) :
-- imply
  (∀ e | p e ∨ q e, f e) ↔ (∀ e | p e, f e) ∧ ∀ e | q e, f e := by
-- proof
  aesop


-- created on 2025-08-04
