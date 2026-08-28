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
  let D : ℤ :=
    ⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉ -
      (
        let U : ℂ := √δc - q
        let V : ℂ := -√δc - q
        if p * (⌈(arg U + arg V) / (2 * π) - 1 / 2⌉ : ℂ) = 0 then
          (0 : ℤ)
        else if arg U + arg V > π then
          1
        else
          -1
      )
  let ω : ℂ := ↑(-(1 / 2 : ℝ)) + ↑(√3 / 2 : ℝ) * I
  (β = 0 →
    let Δ : ℂ := α ^ 2 - 4 * γ
    x = √(√Δ / 2 - α / 2) - a / 4 ∨
      x = -√(√Δ / 2 - α / 2) - a / 4 ∨
      x = √(-√Δ / 2 - α / 2) - a / 4 ∨
      x = -√(-√Δ / 2 - α / 2) - a / 4) ∧
    (β ≠ 0 ∧ D = 0 →
      let y : ℂ := A + B
      let y0 : ℂ := -2 * α / 3 + y
      let y1 : ℂ := 4 * α / 3 + y
      x = √(2 * β / √y0 - y1) / 2 - √y0 / 2 - a / 4 ∨
        x = -√(2 * β / √y0 - y1) / 2 - √y0 / 2 - a / 4 ∨
        x = √(-2 * β / √y0 - y1) / 2 + √y0 / 2 - a / 4 ∨
        x = -√(-2 * β / √y0 - y1) / 2 + √y0 / 2 - a / 4) ∧
    (β ≠ 0 ∧ D % 3 = 1 →
      let y : ℂ := A * ω + B
      let y0 : ℂ := -2 * α / 3 + y
      let y1 : ℂ := 4 * α / 3 + y
      x = √(2 * β / √y0 - y1) / 2 - √y0 / 2 - a / 4 ∨
        x = -√(2 * β / √y0 - y1) / 2 - √y0 / 2 - a / 4 ∨
        x = √(-2 * β / √y0 - y1) / 2 + √y0 / 2 - a / 4 ∨
        x = -√(-2 * β / √y0 - y1) / 2 + √y0 / 2 - a / 4) ∧
    (β ≠ 0 ∧ D % 3 = 2 →
      let y : ℂ := A * ~ω + B
      let y0 : ℂ := -2 * α / 3 + y
      let y1 : ℂ := 4 * α / 3 + y
      x = √(2 * β / √y0 - y1) / 2 - √y0 / 2 - a / 4 ∨
        x = -√(2 * β / √y0 - y1) / 2 - √y0 / 2 - a / 4 ∨
        x = √(-2 * β / √y0 - y1) / 2 + √y0 / 2 - a / 4 ∨
        x = -√(-2 * β / √y0 - y1) / 2 + √y0 / 2 - a / 4) := by
-- proof
  intro α β γ δ U V A B ar br cr p q δc D ω
  let z : ℂ := x + a / 4
  have hx : x = z - a / 4 := by
    simp [z]
  have hz : z ^ 4 + α * z ^ 2 + β * z + γ = 0 := by
    rw [hx] at h
    simp only [α, β, γ] at h ⊢
    convert h using 1
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
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
    intro ⟨hβ, hD⟩ y y0 y1
    have hfour := (ImpEq_0.ImpAnd_Eq_0.ImpAnd_Eq_1.ImpAnd_Eq_2.of.Eq0AddAddAddPow_4 hz).2.1 ⟨hβ, hD⟩
    rcases hfour with hz' | hz' | hz' | hz'
    ·
      exact Or.inl (hx.trans (hz' ▸ rfl))
    ·
      exact Or.inr (Or.inl (hx.trans (hz' ▸ rfl)))
    ·
      exact Or.inr (Or.inr (Or.inl (hx.trans (hz' ▸ rfl))))
    ·
      exact Or.inr (Or.inr (Or.inr (hx.trans (hz' ▸ rfl))))
  ·
    intro ⟨hβ, hD⟩ y y0 y1
    have hfour := (ImpEq_0.ImpAnd_Eq_0.ImpAnd_Eq_1.ImpAnd_Eq_2.of.Eq0AddAddAddPow_4 hz).2.2.1 ⟨hβ, hD⟩
    rcases hfour with hz' | hz' | hz' | hz'
    ·
      exact Or.inl (hx.trans (hz' ▸ rfl))
    ·
      exact Or.inr (Or.inl (hx.trans (hz' ▸ rfl)))
    ·
      exact Or.inr (Or.inr (Or.inl (hx.trans (hz' ▸ rfl))))
    ·
      exact Or.inr (Or.inr (Or.inr (hx.trans (hz' ▸ rfl))))
  ·
    intro ⟨hβ, hD⟩ y y0 y1
    have hfour := (ImpEq_0.ImpAnd_Eq_0.ImpAnd_Eq_1.ImpAnd_Eq_2.of.Eq0AddAddAddPow_4 hz).2.2.2 ⟨hβ, hD⟩
    rcases hfour with hz' | hz' | hz' | hz'
    ·
      exact Or.inl (hx.trans (hz' ▸ rfl))
    ·
      exact Or.inr (Or.inl (hx.trans (hz' ▸ rfl)))
    ·
      exact Or.inr (Or.inr (Or.inl (hx.trans (hz' ▸ rfl))))
    ·
      exact Or.inr (Or.inr (Or.inr (hx.trans (hz' ▸ rfl))))


-- created on 2018-11-28
-- updated on 2026-08-28
