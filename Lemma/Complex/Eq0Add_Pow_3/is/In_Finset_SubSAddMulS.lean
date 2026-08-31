import Lemma.Complex.Eq0Add_Pow_3.is.In_Finset_AddSMulS
import Lemma.Finset.PowAdd.eq.Sum_MulMulPowS
import Lemma.Int.EqSub.is.Eq_Add
import Lemma.Nat.Mul_Add.eq.AddMulS
import Lemma.Set.In_Finset.is.Or_OrEqS
open Complex Finset Int Nat Set


/--
| attributes | lemma |
| :---: | :---: |
| main | Complex.Eq0Add_Pow_3.is.In_Finset_SubSAddMulS |
| comm | Complex.In_Finset_SubSAddMulS.is.Eq0Add_Pow_3 |
| mp | Complex.In_Finset_SubSAddMulS.of.Eq0Add_Pow_3 |
| mpr | Complex.Eq0Add_Pow_3.of.In_Finset_SubSAddMulS |
-/
@[main, comm, mp, mpr]
private lemma main
  {x a b c : ℂ} :
-- imply
  c + b * x + a * x ^ 2 + x ^ 3 = 0 ↔
    let p := b - a ^ 2 / 3
    let q := 2 * a ^ 3 / 27 - a * b / 3 + c
    let δ := 4 * p ^ 3 / 27 + q ^ 2
    let A := ∛((-q + √δ) / 2)
    let B := ∛((-q - √δ) / 2)
    let ω := (I * (2 * π / 3)).exp
    let k := ⌈3 * arg (-p) / (2 * π) - 1 / 2⌉ - ⌈3 * arg (A * B) / (2 * π) - 1 / 2⌉
    x ∈ ({A * ω ^ k + B - a / 3, A * ω ^ (k - 1) + B * ω - a / 3, A * ω ^ (k + 1) + B * ~ω - a / 3} : Set ℂ) := by
-- proof
  extract_lets p q δ A B ω k
  let z := x + a / 3
  rw [(by grind : c + b * x + a * x ^ 2 + x ^ 3 = q + p * z + z ^ 3)]
  apply Iff.trans Eq0Add_Pow_3.is.In_Finset_AddSMulS
  simp only [In_Finset.is.Or_OrEqS, z]
  grind


-- created on 2018-11-25
-- updated on 2026-08-31
