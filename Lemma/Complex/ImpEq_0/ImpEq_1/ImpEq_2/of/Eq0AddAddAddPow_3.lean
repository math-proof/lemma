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
  let ω : ℂ := ↑(-(1 / 2 : ℝ)) + ↑(√3 / 2 : ℝ) * I
  let d : ℤ :=
    ⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉ -
      ⌈3 * arg (U ^ (3 : ℂ)⁻¹ * V ^ (3 : ℂ)⁻¹) / (2 * π) - 1 / 2⌉
  (d = 0 →
      x = A + B - a / 3 ∨
        x = A * ω + B * ~ω - a / 3 ∨
        x = A * ~ω + B * ω - a / 3) ∧
    (d % 3 = 1 →
      x = A * ω + B - a / 3 ∨
        x = A * ~ω + B * ~ω - a / 3 ∨
        x = A + B * ω - a / 3) ∧
    (d % 3 = 2 →
      x = A * ~ω + B - a / 3 ∨
        x = A + B * ~ω - a / 3 ∨
        x = A * ω + B * ω - a / 3) := by
-- proof
  intro p q δ U V A B ω d
  let z : ℂ := x + a / 3
  have hzdef : z = a / 3 + x := by
    simp [z]
    ring
  have hx : x = z - a / 3 := (EqAdd.is.Eq_Sub.left (a / 3) x z).mp hzdef.symm
  have hz : z ^ 3 + p * z + q = 0 := by
    have h' := h
    rw [hx] at h'
    simp only [p, q] at h' ⊢
    convert h' using 1
    have hpow3 := PowAdd.eq.Sum_MulMulPowS (x := z) (y := -(a / 3)) 3
    have hpow2 := PowAdd.eq.Sum_MulMulPowS (x := z) (y := -(a / 3)) 2
    have hmul := Mul_Add.eq.AddMulS b z (-(a / 3))
    rw [← sub_eq_add_neg] at hpow3 hpow2 hmul
    rw [hpow3, hpow2, hmul]
    simp [Finset.sum_range_succ]
    ring
  have hroot := ImpEq_0.ImpEq_1.ImpEq_2.of.Eq0AddAddPow_3 hz
  obtain ⟨h0, h1, h2⟩ := hroot
  refine ⟨?_, ?_, ?_⟩
  ·
    intro hd
    rcases h0 hd with hz' | hz' | hz'
    ·
      exact Or.inl (eq_sub_of_add_eq hz')
    ·
      exact Or.inr (Or.inl (eq_sub_of_add_eq hz'))
    ·
      exact Or.inr (Or.inr (eq_sub_of_add_eq hz'))
  ·
    intro hd
    rcases h1 hd with hz' | hz' | hz'
    ·
      exact Or.inl (eq_sub_of_add_eq hz')
    ·
      exact Or.inr (Or.inl (eq_sub_of_add_eq hz'))
    ·
      exact Or.inr (Or.inr (eq_sub_of_add_eq hz'))
  ·
    intro hd
    rcases h2 hd with hz' | hz' | hz'
    ·
      exact Or.inl (eq_sub_of_add_eq hz')
    ·
      exact Or.inr (Or.inl (eq_sub_of_add_eq hz'))
    ·
      exact Or.inr (Or.inr (eq_sub_of_add_eq hz'))


-- created on 2018-11-25
-- updated on 2026-08-29
