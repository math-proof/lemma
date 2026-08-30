import Lemma.Complex.ImpEq_0.ImpAnd_Eq_0.ImpAnd_Eq_1.ImpAnd_Eq_2.of.Eq0AddAddAddAddPow_4
import Lemma.Nat.Mul.eq.Zero.is.OrEqS_0
open Complex Nat


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
  let p : ℂ := -4 * γ - α ^ 2 / 3
  let q : ℂ := -2 * α ^ 3 / 27 + 8 * α * γ / 3 - β ^ 2
  let δ : ℂ := 4 * p ^ 3 / 27 + q ^ 2
  let A : ℂ := ∛((-q + √δ) / 2)
  let B : ℂ := ∛((-q - √δ) / 2)
  let k : ℤ := ⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉ - ⌈3 * arg (A * B) / (2 * π) - 1 / 2⌉
  let ω : ℂ := (I * (2 * π / 3)).exp
  let y : ℂ := A * ω ^ k + B
  let y0 : ℂ := -2 * α / 3 + y
  let y1 : ℂ := 4 * α / 3 + y
  (β = 0 →
    let Δ : ℂ := α ^ 2 - 4 * γ
    x = √(√Δ / 2 - α / 2) - a' / 4 ∨
      x = -√(√Δ / 2 - α / 2) - a' / 4 ∨
      x = √(-√Δ / 2 - α / 2) - a' / 4 ∨
      x = -√(-√Δ / 2 - α / 2) - a' / 4) ∧
    (β ≠ 0 →
      (x = (√(2 * β / √y0 - y1) - √y0) / 2 - a' / 4 ∨
        x = (-√(2 * β / √y0 - y1) - √y0) / 2 - a' / 4) ∨
        x = (√(-2 * β / √y0 - y1) + √y0) / 2 - a' / 4 ∨
        x = (-√(-2 * β / √y0 - y1) + √y0) / 2 - a' / 4) := by
-- proof
  intro a' b' c' d' α β γ p q δ A B k ω y y0 y1
  apply ImpEq_0.ImpAnd_Eq_0.ImpAnd_Eq_1.ImpAnd_Eq_2.of.Eq0AddAddAddAddPow_4
  apply
    (OrEqS_0.of.Mul.eq.Zero
      (a := a)
      (b := x ^ 4 + a' * x ^ 3 + b' * x ^ 2 + c' * x + d')
      ?_).resolve_left ha
  refine Eq.trans ?_ h
  simp only [a', b', c', d']
  field_simp [ha]


-- created on 2018-11-29
-- updated on 2026-08-29
