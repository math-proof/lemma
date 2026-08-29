import sympy.core.power
import sympy.core.numbers
import sympy.functions.elementary.complexes
import sympy.polys.polyroots
import Lemma.Complex.Or_OrEqS_AddMulS.of.Eq0Add_Pow_3
import Lemma.Finset.PowAdd.eq.Sum_MulMulPowS
import Lemma.Int.EqSub.is.Eq_Add
import Lemma.Nat.Mul_Add.eq.AddMulS
open Complex Finset Int Nat


@[main]
private lemma main
  {x a b c : ℂ}
-- given
  (h : c + b * x + a * x ^ 2 + x ^ 3 = 0) :
-- imply
  let p : ℂ := b - a ^ 2 / 3
  let q : ℂ := 2 * a ^ 3 / 27 - a * b / 3 + c
  let δ : ℂ := 4 * p ^ 3 / 27 + q ^ 2
  let A : ℂ := ((-q + √δ) / 2) ^ (3 : ℂ)⁻¹
  let B : ℂ := ((-q - √δ) / 2) ^ (3 : ℂ)⁻¹
  let ω : ℂ := (I * (2 * π / 3)).exp
  let k : ℤ := ⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉ - ⌈3 * arg (A * B) / (2 * π) - 1 / 2⌉
  x = A * ω ^ k + B - a / 3 ∨
    x = A * ω ^ (k - 1) + B * ω - a / 3 ∨
    x = A * ω ^ (k + 1) + B * ~ω - a / 3 := by
-- proof
  intro p q δ A B ω k
  let z : ℂ := x + a / 3
  have hz : q + p * z + z ^ 3 = 0 := by grind
  obtain hz' | hz' | hz' := Or_OrEqS_AddMulS.of.Eq0Add_Pow_3.cardano hz <;> grind


-- created on 2018-11-25
-- updated on 2026-08-29
