import sympy.functions.elementary.integers
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Nat.Odd.is.Any_Eq_AddMul2 |
| comm | Nat.Any_Eq_AddMul2.is.Odd |
| mp | Nat.Any_Eq_AddMul2.of.Odd |
| mpr | Nat.Odd.of.Any_Eq_AddMul2 |
-/
@[main, comm, mp, mpr]
private lemma main
  [Semiring α]
-- given
  (n : α) :
-- imply
  n is odd ↔ ∃ k, n = 2 * k + 1 :=
-- proof
  odd_iff_exists_bit1


-- created on 2025-03-04
-- updated on 2025-08-13
