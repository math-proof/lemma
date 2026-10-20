import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.GeneralizedFibocatalanNumber
open MetaMathlibExt


/--
[fibonacciFactorial_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedFibocatalanNumber.lean)
-/
@[path]
private lemma fibonacciFactorial_zero_eq
  :
-- imply
  fibonacciFactorial 0 = 1 := by
-- proof
  apply MetaMathlibExt.fibonacciFactorial_zero

/--
[fibonacciFactorial_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedFibocatalanNumber.lean)
-/
@[path]
private lemma fibonacciFactorial_pos_eq
  {n : ℕ} :
-- imply
  0 < fibonacciFactorial n := by
-- proof
  apply MetaMathlibExt.fibonacciFactorial_pos n

/--
[fibonacciFactorial_ne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedFibocatalanNumber.lean)
-/
@[path]
private lemma fibonacciFactorial_ne_eq
  {n : ℕ} :
-- imply
  fibonacciFactorial n ≠ 0 := by
-- proof
  apply MetaMathlibExt.fibonacciFactorial_ne n

/--
[fibonacciFactorial_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedFibocatalanNumber.lean)
-/
@[path]
private lemma fibonacciFactorial_one_eq
  :
-- imply
  fibonacciFactorial 1 = 1 := by
-- proof
  apply MetaMathlibExt.fibonacciFactorial_one

/--
[fibonacciFactorial_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedFibocatalanNumber.lean)
-/
@[path]
private lemma fibonacciFactorial_two_eq
  :
-- imply
  fibonacciFactorial 2 = 1 := by
-- proof
  apply MetaMathlibExt.fibonacciFactorial_two

/--
[fibonacciFactorial_three](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedFibocatalanNumber.lean)
-/
@[path]
private lemma fibonacciFactorial_three_eq
  :
-- imply
  fibonacciFactorial 3 = 2 := by
-- proof
  apply MetaMathlibExt.fibonacciFactorial_three

/--
[fibonacciJordanQuotient_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedFibocatalanNumber.lean)
-/
@[path]
private lemma fibonacciJordanQuotient_pos_eq
  {r : ℕ} :
-- imply
  0 < fibonacciJordanQuotient r := by
-- proof
  apply MetaMathlibExt.fibonacciJordanQuotient_pos r

/--
[fibonacciJordanQuotient_r0](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedFibocatalanNumber.lean)
-/
@[path]
private lemma fibonacciJordanQuotient_r0_eq
  :
-- imply
  fibonacciJordanQuotient 0 = 1 := by
-- proof
  apply MetaMathlibExt.fibonacciJordanQuotient_r0

/--
[fibonacciJordanQuotient_r1](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedFibocatalanNumber.lean)
-/
@[path]
private lemma fibonacciJordanQuotient_r1_eq
  :
-- imply
  fibonacciJordanQuotient 1 = 2 := by
-- proof
  apply MetaMathlibExt.fibonacciJordanQuotient_r1

/--
[generalizedFibonacciCatalan_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedFibocatalanNumber.lean)
-/
@[path]
private lemma generalizedFibonacciCatalan_pos_eq
  {r n : ℕ} :
-- imply
  0 < generalizedFibonacciCatalan r n := by
-- proof
  apply MetaMathlibExt.generalizedFibonacciCatalan_pos r n

/--
[generalizedFibonacciCatalan_isPosInt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedFibocatalanNumber.lean)
-/
@[path]
private lemma generalizedFibonacciCatalan_isPosInt_eq
  {r n : ℕ} :
-- imply
  ∃ k : ℕ, 0 < k ∧ (k : ℚ) = generalizedFibonacciCatalan r n := by
-- proof
  apply MetaMathlibExt.generalizedFibonacciCatalan_isPosInt r n

/--
[generalizedFibonacciCatalan_r0](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedFibocatalanNumber.lean)
-/
@[path]
private lemma generalizedFibonacciCatalan_r0_eq
  {n : ℕ} :
-- imply
  generalizedFibonacciCatalan 0 n =
    fibonacciFactorial (2 * n) /
    (fibonacciFactorial n * fibonacciFactorial (n + 1)) := by
-- proof
  apply MetaMathlibExt.generalizedFibonacciCatalan_r0 n

/--
[generalizedFibonacciCatalan_r1](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedFibocatalanNumber.lean)
-/
@[path]
private lemma generalizedFibonacciCatalan_r1_eq
  {n : ℕ} :
-- imply
  generalizedFibonacciCatalan 1 n =
    2 * fibonacciFactorial (2 * n) /
    (fibonacciFactorial (n + 2) * fibonacciFactorial n) := by
-- proof
  apply MetaMathlibExt.generalizedFibonacciCatalan_r1 n


-- created on 2026-10-20
