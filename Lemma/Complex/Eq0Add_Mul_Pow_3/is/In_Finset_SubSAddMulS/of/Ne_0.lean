import Lemma.Complex.Eq0Add_Pow_3.is.In_Finset_SubSAddMulS
open Complex


/--
| attributes | lemma |
| :---: | :---: |
| main | Complex.Eq0Add_Mul_Pow_3.is.In_Finset_SubSAddMulS.of.Ne_0 |
| comm | Complex.In_Finset_SubSAddMulS.is.Eq0Add_Mul_Pow_3.of.Ne_0 |
| mp | Complex.In_Finset_SubSAddMulS.of.Eq0Add_Mul_Pow_3.Ne_0 |
| mpr | Complex.Eq0Add_Mul_Pow_3.of.In_Finset_SubSAddMulS.Ne_0 |
-/
@[main, comm, mp, mpr]
private lemma main
  {x a b c d : ℂ}
-- given
  (ha : a ≠ 0) :
-- imply
  d + c * x + b * x ^ 2 + a * x ^ 3 = 0 ↔
    let a' := b / a
    let b' := c / a
    let c' := d / a
    let p := b' - a' ^ 2 / 3
    let q := 2 * a' ^ 3 / 27 - a' * b' / 3 + c'
    let δ := 4 * p ^ 3 / 27 + q ^ 2
    let A := ∛((-q + √δ) / 2)
    let B := ∛((-q - √δ) / 2)
    let ω := (I * (2 * π / 3)).exp
    let k := ⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉ - ⌈3 * arg (A * B) / (2 * π) - 1 / 2⌉
    x ∈ ({A * ω ^ k + B - a' / 3, A * ω ^ (k - 1) + B * ω - a' / 3, A * ω ^ (k + 1) + B * ~ω - a' / 3} : Set ℂ) := by
-- proof
  apply Iff.trans ?_ Eq0Add_Pow_3.is.In_Finset_SubSAddMulS
  grind


-- created on 2018-11-25
-- updated on 2026-08-31
