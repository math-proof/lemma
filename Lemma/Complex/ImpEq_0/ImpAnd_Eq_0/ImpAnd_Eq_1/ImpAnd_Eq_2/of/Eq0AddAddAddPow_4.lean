import Lemma.Complex.OrOrSEqS.of.Eq0AddAddPow_4
import Lemma.Complex.OrOrSEqS_Div_2.of.Eq0Add_Pow_4.Ne_0
open Complex


@[main]
private lemma main
  {x α β γ : ℂ}
-- given
  (h : x ^ 4 + α * x ^ 2 + β * x + γ = 0) :
-- imply
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
    x = √(√Δ / 2 - α / 2) ∨
      x = -√(√Δ / 2 - α / 2) ∨
      x = √(-√Δ / 2 - α / 2) ∨
      x = -√(-√Δ / 2 - α / 2)) ∧
    (β ≠ 0 →
      (x = (√(2 * β / √y0 - y1) - √y0) / 2 ∨
        x = (-√(2 * β / √y0 - y1) - √y0) / 2) ∨
        x = (√(-2 * β / √y0 - y1) + √y0) / 2 ∨
        x = (-√(-2 * β / √y0 - y1) + √y0) / 2) := by
-- proof
  intro p q δ A B k ω y y0 y1
  refine ⟨?_, ?_⟩
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
    intro hβ
    have : γ + β * x + α * x ^ 2 + x ^ 4 = 0 := by
      rw [(by ring : γ + β * x + α * x ^ 2 + x ^ 4 = x ^ 4 + α * x ^ 2 + β * x + γ)]
      apply h
    apply OrOrSEqS_Div_2.of.Eq0Add_Pow_4.Ne_0.ferrari hβ this


-- created on 2018-11-27
-- updated on 2026-08-29
