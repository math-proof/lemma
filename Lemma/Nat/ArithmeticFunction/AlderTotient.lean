import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.ArithmeticFunction.AlderTotient
open ArithmeticFunction


/--
[alderTotientTwo_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/AlderTotient.lean)
-/
@[path]
private lemma alderTotientTwo_apply_eq
  {k : ℕ} :
-- imply
  alderTotientTwo k =
      ((Finset.range k).filter fun r =>
        Nat.Coprime k r ∧ Nat.Coprime k (2 * r + 1)).card := by
-- proof
  apply ArithmeticFunction.alderTotientTwo_apply k

/--
[alderTotientTwo_succ_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/AlderTotient.lean)
-/
@[path]
private lemma alderTotientTwo_succ_apply_eq
  {k : ℕ} :
-- imply
  alderTotientTwo (k + 1) =
      ((Finset.range (k + 1)).filter fun r =>
        Nat.Coprime r (k + 1) ∧ Nat.Coprime (2 * r + 1) (k + 1)).card := by
-- proof
  apply ArithmeticFunction.alderTotientTwo_succ_apply k

/--
[alderTotientTwo_succ_Iic_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/AlderTotient.lean)
-/
@[path]
private lemma alderTotientTwo_succ_Iic_apply_eq
  {k : ℕ} :
-- imply
  alderTotientTwo (k + 1) =
      ((Finset.Iic k).filter fun r =>
        Nat.Coprime r (k + 1) ∧ Nat.Coprime (2 * r + 1) (k + 1)).card := by
-- proof
  apply ArithmeticFunction.alderTotientTwo_succ_Iic_apply k

/--
[alderTotientTwo_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/AlderTotient.lean)
-/
@[path]
private lemma alderTotientTwo_zero_eq
  :
-- imply
  alderTotientTwo 0 = 0 := by
-- proof
  apply ArithmeticFunction.alderTotientTwo_zero

/--
[alderTotientTwo_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/AlderTotient.lean)
-/
@[path]
private lemma alderTotientTwo_one_eq
  :
-- imply
  alderTotientTwo 1 = 1 := by
-- proof
  apply ArithmeticFunction.alderTotientTwo_one

/--
[alderTotientTwo_le_totient](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/AlderTotient.lean)
-/
@[path]
private lemma alderTotientTwo_le_totient_eq
  {k : ℕ} :
-- imply
  alderTotientTwo k ≤ Nat.totient k := by
-- proof
  apply ArithmeticFunction.alderTotientTwo_le_totient k


-- created on 2026-10-20
