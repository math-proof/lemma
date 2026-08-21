import sympy.core.power
import sympy.core.numbers
import sympy.polys.polyroots
import Lemma.Algebra.Or.Eq.of.Add.eq.Zero.Eq_Ceil.cubic
open Algebra


@[main]
private lemma main
  {x a b c : ℂ}
-- given
  (h : x ^ 3 + a * x ^ 2 + b * x + c = 0) :
-- imply
  let p : ℂ := b - a ^ 2 / 3
  let q : ℂ := 2 * a ^ 3 / 27 - a * b / 3 + c
  let δ : ℂ := 4 * p ^ 3 / 27 + q ^ 2
  let A : ℂ := (√δ / 2 - q / 2) ^ (3 : ℂ)⁻¹
  let B : ℂ := (-√δ / 2 - q / 2) ^ (3 : ℂ)⁻¹
  let d : ℤ :=
    ⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉ -
      ⌈3 * arg (A * B) / (2 * π) - 1 / 2⌉
  let ω : ℂ := ↑(-(1 / 2 : ℝ)) + ↑(√3 / 2 : ℝ) * I
  (d = 0 →
      x = A + B - a / 3 ∨
        x = A * ω + B * (starRingEnd ℂ) ω - a / 3 ∨
        x = A * (starRingEnd ℂ) ω + B * ω - a / 3) ∧
    (d % 3 = 1 →
      x = A * ω + B - a / 3 ∨
        x = A * (starRingEnd ℂ) ω + B * (starRingEnd ℂ) ω - a / 3 ∨
        x = A + B * ω - a / 3) ∧
    (d % 3 = 2 →
      x = A * (starRingEnd ℂ) ω + B - a / 3 ∨
        x = A + B * (starRingEnd ℂ) ω - a / 3 ∨
        x = A * ω + B * ω - a / 3) := by
-- proof
  intro p q δ A B d ω
  let z : ℂ := x + a / 3
  have hx : x = z - a / 3 := by
    simp [z]
  have hz : z ^ 3 + p * z + q = 0 := by
    have h' := h
    rw [hx] at h'
    simp only [p, q] at h' ⊢
    convert h' using 1
    ring
  have hroot := Or.Eq.of.Add.eq.Zero.Eq_Ceil.cubic hz
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
-- updated on 2026-08-20
