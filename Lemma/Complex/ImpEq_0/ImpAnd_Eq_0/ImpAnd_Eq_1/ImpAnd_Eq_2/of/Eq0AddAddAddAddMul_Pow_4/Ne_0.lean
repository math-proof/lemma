import sympy.core.power
import sympy.core.numbers
import sympy.polys.polyroots
import Lemma.Algebra.Or_Eq.of.Add.eq.Zero.biquadratic
import Lemma.Algebra.And.Imp.Or.Eq.of.Add.eq.Zero.cubic.one_leaded
open Algebra


@[main]
private lemma main
  {x a b c d e : ℂ}
-- given
  (ha : a ≠ 0)
  (h : a * x ^ 4 + b * x ^ 3 + c * x ^ 2 + d * x + e = 0) :
-- imply
  let a' : ℂ := b / a
  let b' : ℂ := c / a
  let c' : ℂ := d / a
  let d' : ℂ := e / a
  let α : ℂ := b' - 3 * a' ^ 2 / 8
  let β : ℂ := a' ^ 3 / 8 + c' - a' * b' / 2
  let γ : ℂ := a' ^ 2 * b' / 16 + d' - 3 * a' ^ 4 / 256 - a' * c' / 4
  let δ : ℂ :=
    -(α ^ 2 / 3 + 4 * γ) ^ 3 / 27 +
      (-α ^ 3 / 27 + 4 * α * γ / 3 - β ^ 2 / 2) ^ 2
  let U : ℂ := α ^ 3 / 27 - 4 * α * γ / 3 + β ^ 2 / 2 + √δ
  let V : ℂ := α ^ 3 / 27 - 4 * α * γ / 3 + β ^ 2 / 2 - √δ
  let A : ℂ := U ^ (3 : ℂ)⁻¹
  let B : ℂ := V ^ (3 : ℂ)⁻¹
  let ar : ℂ := -α / 2
  let br : ℂ := -γ
  let cr : ℂ := -β ^ 2 / 8 + α * γ / 2
  let p : ℂ := br - ar ^ 2 / 3
  let q : ℂ := 2 * ar ^ 3 / 27 - ar * br / 3 + cr
  let δc : ℂ := 4 * p ^ 3 / 27 + q ^ 2
  let Ac : ℂ := (√δc / 2 - q / 2) ^ (3 : ℂ)⁻¹
  let Bc : ℂ := (-√δc / 2 - q / 2) ^ (3 : ℂ)⁻¹
  let D : ℤ :=
    ⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉ -
      ⌈3 * arg (Ac * Bc) / (2 * π) - 1 / 2⌉
  let ω : ℂ := ↑(-(1 / 2 : ℝ)) + ↑(√3 / 2 : ℝ) * I
  (β = 0 →
    let Δ : ℂ := α ^ 2 - 4 * γ
    x = √(√Δ / 2 - α / 2) - a' / 4 ∨
      x = -√(√Δ / 2 - α / 2) - a' / 4 ∨
      x = √(-√Δ / 2 - α / 2) - a' / 4 ∨
      x = -√(-√Δ / 2 - α / 2) - a' / 4) ∧
    (β ≠ 0 ∧ D = 0 →
      let y : ℂ := A + B
      let y0 : ℂ := -2 * α / 3 + y
      let y1 : ℂ := 4 * α / 3 + y
      x = √(2 * β / √y0 - y1) / 2 - √y0 / 2 - a' / 4 ∨
        x = -√(2 * β / √y0 - y1) / 2 - √y0 / 2 - a' / 4 ∨
        x = √(-2 * β / √y0 - y1) / 2 + √y0 / 2 - a' / 4 ∨
        x = -√(-2 * β / √y0 - y1) / 2 + √y0 / 2 - a' / 4) ∧
    (β ≠ 0 ∧ D % 3 = 1 →
      let y : ℂ := A * ω + B
      let y0 : ℂ := -2 * α / 3 + y
      let y1 : ℂ := 4 * α / 3 + y
      x = √(2 * β / √y0 - y1) / 2 - √y0 / 2 - a' / 4 ∨
        x = -√(2 * β / √y0 - y1) / 2 - √y0 / 2 - a' / 4 ∨
        x = √(-2 * β / √y0 - y1) / 2 + √y0 / 2 - a' / 4 ∨
        x = -√(-2 * β / √y0 - y1) / 2 + √y0 / 2 - a' / 4) ∧
    (β ≠ 0 ∧ D % 3 = 2 →
      let y : ℂ := A * (starRingEnd ℂ) ω + B
      let y0 : ℂ := -2 * α / 3 + y
      let y1 : ℂ := 4 * α / 3 + y
      x = √(2 * β / √y0 - y1) / 2 - √y0 / 2 - a' / 4 ∨
        x = -√(2 * β / √y0 - y1) / 2 - √y0 / 2 - a' / 4 ∨
        x = √(-2 * β / √y0 - y1) / 2 + √y0 / 2 - a' / 4 ∨
        x = -√(-2 * β / √y0 - y1) / 2 + √y0 / 2 - a' / 4) := by
-- proof
  intro a' b' c' d' α β γ δ U V A B ar br cr p q δc Ac Bc D ω
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro hβ Δ
    let z : ℂ := x + a' / 4
    have hx : x = z - a' / 4 := by
      simp [z]
    have hz : z ^ 4 + α * z ^ 2 + γ = 0 := by
      have hmonic : x ^ 4 + a' * x ^ 3 + b' * x ^ 2 + c' * x + d' = 0 := by
        have hmul :
            a * (x ^ 4 + (b / a) * x ^ 3 + (c / a) * x ^ 2 + (d / a) * x + e / a) =
              a * x ^ 4 + b * x ^ 3 + c * x ^ 2 + d * x + e := by
          field_simp [ha]
        have h0 : a * (x ^ 4 + a' * x ^ 3 + b' * x ^ 2 + c' * x + d') = 0 := by
          simp only [a', b', c', d']
          rw [hmul, h]
        exact (mul_eq_zero.mp h0).resolve_left ha
      rw [hx] at hmonic
      have hexp :
          (z - a' / 4) ^ 4 + a' * (z - a' / 4) ^ 3 + b' * (z - a' / 4) ^ 2 +
              c' * (z - a' / 4) + d' =
            z ^ 4 + α * z ^ 2 + β * z + γ := by
        simp only [α, β, γ]
        ring
      rw [hexp, hβ] at hmonic
      simpa using hmonic
    have hbi := Or_Eq.of.Add.eq.Zero.biquadratic (x := z) (α := α) (γ := γ) hz
    rcases hbi with hz' | hz' | hz' | hz'
    ·
      exact Or.inl (eq_sub_of_add_eq hz')
    ·
      exact Or.inr (Or.inl (eq_sub_of_add_eq hz'))
    ·
      exact Or.inr (Or.inr (Or.inl (eq_sub_of_add_eq hz')))
    ·
      exact Or.inr (Or.inr (Or.inr (eq_sub_of_add_eq hz')))
  ·
    sorry
  ·
    sorry
  ·
    sorry


-- created on 2018-11-29
-- updated on 2026-08-21
