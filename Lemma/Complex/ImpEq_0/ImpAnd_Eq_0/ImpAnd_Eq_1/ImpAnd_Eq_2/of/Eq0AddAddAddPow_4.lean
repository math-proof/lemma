import Lemma.Complex.OrOrSEqS.of.Eq0AddAddPow_4
import Lemma.Complex.ImpEq_0.ImpAnd_Eq_0.ImpAnd_Eq_1.ImpAnd_Eq_2.of.Eq0AddAddAddMul_Pow_4.Ne_0
open Complex


@[main]
private lemma main
  {x α β γ : ℂ}
-- given
  (h : x ^ 4 + α * x ^ 2 + β * x + γ = 0) :
-- imply
  let δ : ℂ := -(α ^ 2 / 3 + 4 * γ) ^ 3 / 27 + (-α ^ 3 / 27 + 4 * α * γ / 3 - β ^ 2 / 2) ^ 2
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
    x = √(√Δ / 2 - α / 2) ∨
      x = -√(√Δ / 2 - α / 2) ∨
      x = √(-√Δ / 2 - α / 2) ∨
      x = -√(-√Δ / 2 - α / 2)) ∧
    (β ≠ 0 ∧ D = 0 →
      let y : ℂ := A + B
      let y0 : ℂ := -2 * α / 3 + y
      let y1 : ℂ := 4 * α / 3 + y
      x = √(2 * β / √y0 - y1) / 2 - √y0 / 2 ∨
        x = -√(2 * β / √y0 - y1) / 2 - √y0 / 2 ∨
        x = √(-2 * β / √y0 - y1) / 2 + √y0 / 2 ∨
        x = -√(-2 * β / √y0 - y1) / 2 + √y0 / 2) ∧
    (β ≠ 0 ∧ D % 3 = 1 →
      let y : ℂ := A * ω + B
      let y0 : ℂ := -2 * α / 3 + y
      let y1 : ℂ := 4 * α / 3 + y
      x = √(2 * β / √y0 - y1) / 2 - √y0 / 2 ∨
        x = -√(2 * β / √y0 - y1) / 2 - √y0 / 2 ∨
        x = √(-2 * β / √y0 - y1) / 2 + √y0 / 2 ∨
        x = -√(-2 * β / √y0 - y1) / 2 + √y0 / 2) ∧
    (β ≠ 0 ∧ D % 3 = 2 →
      let y : ℂ := A * ~ω + B
      let y0 : ℂ := -2 * α / 3 + y
      let y1 : ℂ := 4 * α / 3 + y
      x = √(2 * β / √y0 - y1) / 2 - √y0 / 2 ∨
        x = -√(2 * β / √y0 - y1) / 2 - √y0 / 2 ∨
        x = √(-2 * β / √y0 - y1) / 2 + √y0 / 2 ∨
        x = -√(-2 * β / √y0 - y1) / 2 + √y0 / 2) := by
-- proof
  intro δ U V A B ar br cr p q δc D ω
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro hβ Δ
    have hbq : x ^ 4 + α * x ^ 2 + γ = 0 := by
      simpa [hβ] using h
    have hbi := OrOrSEqS.of.Eq0AddAddPow_4.biquadratic hbq
    simpa [Δ] using show
        x = √(√Δ / 2 - α / 2) ∨
          x = -√(√Δ / 2 - α / 2) ∨
          x = √(-√Δ / 2 - α / 2) ∨
          x = -√(-√Δ / 2 - α / 2) from by
      rcases hbi with (hx | hx) | hx | hx
      · exact Or.inl hx
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr (Or.inl hx))
      · exact Or.inr (Or.inr (Or.inr hx))
  ·
    intro ⟨hβ, hD⟩ y y0 y1
    exact (ImpEq_0.ImpAnd_Eq_0.ImpAnd_Eq_1.ImpAnd_Eq_2.of.Eq0AddAddAddMul_Pow_4.Ne_0 h hβ).1 hD
  ·
    intro ⟨hβ, hD⟩ y y0 y1
    exact (ImpEq_0.ImpAnd_Eq_0.ImpAnd_Eq_1.ImpAnd_Eq_2.of.Eq0AddAddAddMul_Pow_4.Ne_0 h hβ).2.1 hD
  ·
    intro ⟨hβ, hD⟩ y y0 y1
    exact (ImpEq_0.ImpAnd_Eq_0.ImpAnd_Eq_1.ImpAnd_Eq_2.of.Eq0AddAddAddMul_Pow_4.Ne_0 h hβ).2.2 hD


-- created on 2018-11-27
-- updated on 2026-08-28
