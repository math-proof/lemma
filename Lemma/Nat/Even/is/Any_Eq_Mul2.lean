import sympy.functions.elementary.integers
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Nat.Even.is.Any_Eq_Mul2 |
| comm | Nat.Any_Eq_Mul2.is.Even |
| mp | Nat.Any_Eq_Mul2.of.Even |
| mpr | Nat.Even.of.Any_Eq_Mul2 |
-/
@[main, comm, mp, mpr]
private lemma main
  [Semiring α]
-- given
  (n : α) :
-- imply
  n is even ↔ ∃ k, n = 2 * k :=
-- proof
  even_iff_exists_two_mul


-- created on 2025-08-13
