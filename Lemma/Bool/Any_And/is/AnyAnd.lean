import sympy.concrete.quantifier
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.Any_And.is.AnyAnd |
| comm | Bool.AnyAnd.is.Any_And |
| mp | Bool.AnyAnd.of.Any_And |
| mpr | Bool.Any_And.of.AnyAnd |
-/
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
