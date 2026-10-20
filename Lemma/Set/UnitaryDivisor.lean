import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.UnitaryDivisor
open Nat
open Set


/--
[mem_unitaryDivisors](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/UnitaryDivisor.lean)
-/
@[path]
private lemma mem_unitaryDivisors_eq
  {n d : ℕ} :
-- imply
  d ∈ unitaryDivisors n ↔ d ∣ n ∧ n ≠ 0 ∧ d.Coprime (n / d) := by
-- proof
  apply Nat.mem_unitaryDivisors

/--
[unitaryDivisors_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/UnitaryDivisor.lean)
-/
@[path]
private lemma unitaryDivisors_zero_eq
  :
-- imply
  unitaryDivisors 0 = ∅ := by
-- proof
  apply Nat.unitaryDivisors_zero

/--
[dvd_of_mem_unitaryDivisors](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/UnitaryDivisor.lean)
-/
@[path]
private lemma dvd_of_mem_unitaryDivisors_eq
  {n d : ℕ}
-- given
  (h : d ∈ unitaryDivisors n) :
-- imply
  d ∣ n := by
-- proof
  apply Nat.dvd_of_mem_unitaryDivisors h

/--
[coprime_div_of_mem_unitaryDivisors](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/UnitaryDivisor.lean)
-/
@[path]
private lemma coprime_div_of_mem_unitaryDivisors_eq
  {n d : ℕ}
-- given
  (h : d ∈ unitaryDivisors n) :
-- imply
  d.Coprime (n / d) := by
-- proof
  apply Nat.coprime_div_of_mem_unitaryDivisors h

/--
[sigmaStar_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/UnitaryDivisor.lean)
-/
@[path]
private lemma sigmaStar_eq_sum_eq
  {n : ℕ} :
-- imply
  sigmaStar n = ∑ d ∈ unitaryDivisors n, d := by
-- proof
  apply Nat.sigmaStar_eq_sum n

/--
[sigmaStar_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/UnitaryDivisor.lean)
-/
@[path]
private lemma sigmaStar_zero_eq
  :
-- imply
  sigmaStar 0 = 0 := by
-- proof
  apply Nat.sigmaStar_zero

/--
[isPrimitiveByDivisibility_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/UnitaryDivisor.lean)
-/
@[path]
private lemma isPrimitiveByDivisibility_iff_eq
  {S : Set ℕ}
  {n : ℕ} :
-- imply
  S.IsPrimitiveByDivisibility n ↔
      n ∈ S ∧ ∀ {d : ℕ}, d ∣ n → d < n → d ∉ S := by
-- proof
  apply Set.isPrimitiveByDivisibility_iff

/--
[IsPrimitiveByDivisibility.mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/UnitaryDivisor.lean)
-/
@[path]
private lemma IsPrimitiveByDivisibility_mem_eq
  {S : Set ℕ}
  {n : ℕ}
-- given
  (h : S.IsPrimitiveByDivisibility n) :
-- imply
  n ∈ S := by
-- proof
  apply Set.IsPrimitiveByDivisibility.mem h

/--
[IsPrimitiveByDivisibility.not_mem_of_dvd_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/UnitaryDivisor.lean)
-/
@[path]
private lemma IsPrimitiveByDivisibility_not_mem_of_dvd_lt_eq
  {S : Set ℕ}
  {n d : ℕ}
-- given
  (h : S.IsPrimitiveByDivisibility n)
  (hdvd : d ∣ n)
  (hdn : d < n) :
-- imply
  d ∉ S := by
-- proof
  apply Set.IsPrimitiveByDivisibility.not_mem_of_dvd_lt h hdvd hdn


-- created on 2026-10-20
