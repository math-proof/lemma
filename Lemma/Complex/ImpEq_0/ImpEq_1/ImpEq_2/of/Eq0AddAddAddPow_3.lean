import sympy.core.power
import sympy.core.numbers
import sympy.functions.elementary.complexes
import sympy.polys.polyroots
import Lemma.Complex.ImpEq_0.ImpEq_1.ImpEq_2.of.Eq0AddAddPow_3
import Lemma.Finset.PowAdd.eq.Sum_MulMulPowS
import Lemma.Int.EqSub.is.Eq_Add
import Lemma.Nat.Mul_Add.eq.AddMulS
open Complex
open Finset
open Int
open Nat


@[main]
private lemma main
  {x a b c : ℂ}
-- given
  (h : x ^ 3 + a * x ^ 2 + b * x + c = 0) :
-- imply
  let p : ℂ := b - a ^ 2 / 3
  let q : ℂ := 2 * a ^ 3 / 27 - a * b / 3 + c
  let δ : ℂ := 4 * p ^ 3 / 27 + q ^ 2
  let U : ℂ := √δ - q
  let V : ℂ := -√δ - q
  let A : ℂ := (√δ / 2 - q / 2) ^ (3 : ℂ)⁻¹
  let B : ℂ := (-√δ / 2 - q / 2) ^ (3 : ℂ)⁻¹
  let ω : ℂ := (I * (2 * π / 3)).exp
  let d : ℤ :=
    ⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉ -
      ⌈3 * arg (U ^ (3 : ℂ)⁻¹ * V ^ (3 : ℂ)⁻¹) / (2 * π) - 1 / 2⌉
  x = A * ω ^ d + B - a / 3 ∨
    x = A * ω ^ (d - 1) + B * ω - a / 3 ∨
    x = A * ω ^ (d + 1) + B * ~ω - a / 3 := by
-- proof
  intro p q δ U V A B ω d
  let z : ℂ := x + a / 3
  have hz : z ^ 3 + p * z + q = 0 := by grind
  obtain hz' | hz' | hz' := ImpEq_0.ImpEq_1.ImpEq_2.of.Eq0AddAddPow_3 hz <;> grind


-- created on 2018-11-25
-- updated on 2026-08-29
