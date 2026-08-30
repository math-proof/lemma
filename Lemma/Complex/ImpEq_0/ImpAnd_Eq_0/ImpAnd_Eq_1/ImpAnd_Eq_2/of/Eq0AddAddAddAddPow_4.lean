import sympy.core.power
import sympy.core.numbers
import sympy.functions.elementary.complexes
import sympy.polys.polyroots
import Lemma.Complex.ImpEq_0.ImpAnd_Eq_0.ImpAnd_Eq_1.ImpAnd_Eq_2.of.Eq0AddAddAddPow_4
open Complex


@[main]
private lemma main
  {x a b c d : ℂ}
-- given
  (h : x ^ 4 + a * x ^ 3 + b * x ^ 2 + c * x + d = 0) :
-- imply
  let α : ℂ := b - 3 * a ^ 2 / 8
  let β : ℂ := a ^ 3 / 8 + c - a * b / 2
  let γ : ℂ := a ^ 2 * b / 16 + d - 3 * a ^ 4 / 256 - a * c / 4
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
    x = √(√Δ / 2 - α / 2) - a / 4 ∨
      x = -√(√Δ / 2 - α / 2) - a / 4 ∨
      x = √(-√Δ / 2 - α / 2) - a / 4 ∨
      x = -√(-√Δ / 2 - α / 2) - a / 4) ∧
    (β ≠ 0 →
      (x = (√(2 * β / √y0 - y1) - √y0) / 2 - a / 4 ∨
        x = (-√(2 * β / √y0 - y1) - √y0) / 2 - a / 4) ∨
        x = (√(-2 * β / √y0 - y1) + √y0) / 2 - a / 4 ∨
        x = (-√(-2 * β / √y0 - y1) + √y0) / 2 - a / 4) := by
-- proof
  intro α β γ p q δ A B k ω y y0 y1
  let z : ℂ := x + a / 4
  have hx : x = z - a / 4 := by
    simp [z]
  have hz : z ^ 4 + α * z ^ 2 + β * z + γ = 0 := by
    rw [hx] at h
    simp only [α, β, γ] at h ⊢
    convert h using 1
    ring
  refine ⟨?_, ?_⟩
  ·
    intro hβ Δ
    have hfour := (ImpEq_0.ImpAnd_Eq_0.ImpAnd_Eq_1.ImpAnd_Eq_2.of.Eq0AddAddAddPow_4 hz).1 hβ
    rcases hfour with hz' | hz' | hz' | hz'
    ·
      exact Or.inl (eq_sub_of_add_eq hz')
    ·
      exact Or.inr (Or.inl (eq_sub_of_add_eq hz'))
    ·
      exact Or.inr (Or.inr (Or.inl (eq_sub_of_add_eq hz')))
    ·
      exact Or.inr (Or.inr (Or.inr (eq_sub_of_add_eq hz')))
  ·
    intro hβ
    have hfour := (ImpEq_0.ImpAnd_Eq_0.ImpAnd_Eq_1.ImpAnd_Eq_2.of.Eq0AddAddAddPow_4 hz).2 hβ
    obtain (hz' | hz') | hz' | hz' := hfour
    ·
      exact Or.inl (Or.inl (hx.trans (hz' ▸ rfl)))
    ·
      exact Or.inl (Or.inr (hx.trans (hz' ▸ rfl)))
    ·
      exact Or.inr (Or.inl (hx.trans (hz' ▸ rfl)))
    ·
      exact Or.inr (Or.inr (hx.trans (hz' ▸ rfl)))


-- created on 2018-11-28
-- updated on 2026-08-29
