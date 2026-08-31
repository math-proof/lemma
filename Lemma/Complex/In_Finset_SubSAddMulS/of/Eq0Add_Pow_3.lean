import Lemma.Complex.Eq0Add_Pow_3.is.In_Finset_AddSMulS
import Lemma.Finset.PowAdd.eq.Sum_MulMulPowS
import Lemma.Int.EqSub.is.Eq_Add
import Lemma.Nat.Mul_Add.eq.AddMulS
import Lemma.Set.In_Finset.is.Or_OrEqS
open Complex Finset Int Nat Set


@[main]
private lemma main
  {x a b c : ℂ}
-- given
  (h : c + b * x + a * x ^ 2 + x ^ 3 = 0) :
-- imply
  let p := b - a ^ 2 / 3
  let q := 2 * a ^ 3 / 27 - a * b / 3 + c
  let δ := 4 * p ^ 3 / 27 + q ^ 2
  let A := ∛((-q + √δ) / 2)
  let B := ∛((-q - √δ) / 2)
  let ω := (I * (2 * π / 3)).exp
  let k := ⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉ - ⌈3 * arg (A * B) / (2 * π) - 1 / 2⌉
  x ∈ ({A * ω ^ k + B - a / 3, A * ω ^ (k - 1) + B * ω - a / 3, A * ω ^ (k + 1) + B * ~ω - a / 3} : Set ℂ) := by
-- proof
  intro p q δ A B ω k
  let z := x + a / 3
  have hz : q + p * z + z ^ 3 = 0 := by grind
  rw [In_Finset.is.Or_OrEqS]
  obtain hz' | hz' | hz' := Or_OrEqS.of.In_Finset (In_Finset_AddSMulS.of.Eq0Add_Pow_3 hz) <;> grind


-- created on 2018-11-25
-- updated on 2026-08-31
