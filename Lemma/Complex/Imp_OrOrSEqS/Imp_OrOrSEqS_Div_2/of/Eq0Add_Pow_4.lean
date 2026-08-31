import Lemma.Complex.OrOrSEqS.of.Eq0Add_Pow_4
import Lemma.Complex.OrOrSEqS_Div_2.of.Eq0Add_Pow_4.Ne_0
open Complex


@[main]
private lemma main
  {x α β γ : ℂ}
-- given
  (h : γ + β * x + α * x ^ 2 + x ^ 4 = 0) :
-- imply
  (β = 0 →
    let Δ := α ^ 2 - 4 * γ
    (x = √((√Δ - α) / 2) ∨
      x = -√((√Δ - α) / 2)) ∨
      x = √((-√Δ - α) / 2) ∨
      x = -√((-√Δ - α) / 2)) ∧
    (β ≠ 0 →
      let p := -4 * γ - α ^ 2 / 3
      let q := -2 * α ^ 3 / 27 + 8 * α * γ / 3 - β ^ 2
      let δ := 4 * p ^ 3 / 27 + q ^ 2
      let A := ∛((-q + √δ) / 2)
      let B := ∛((-q - √δ) / 2)
      let k := ⌈3 * arg (-p) / (2 * π) - 1 / 2⌉ - ⌈3 * arg (A * B) / (2 * π) - 1 / 2⌉
      let ω := (I * (2 * π / 3)).exp
      let y := A * ω ^ k + B
      let y0 := -2 * α / 3 + y
      let y1 := 4 * α / 3 + y
      (x = (√(2 * β / √y0 - y1) - √y0) / 2 ∨
        x = (-√(2 * β / √y0 - y1) - √y0) / 2) ∨
        x = (√(-2 * β / √y0 - y1) + √y0) / 2 ∨
        x = (-√(-2 * β / √y0 - y1) + √y0) / 2) := by
-- proof
  extract_lets Δ p q δ A B k ω y y0 y1
  refine ⟨?_, ?_⟩
  ·
    intro hβ
    apply OrOrSEqS.of.Eq0Add_Pow_4.biquadratic
    simpa [hβ] using h
  ·
    intro hβ
    apply OrOrSEqS_Div_2.of.Eq0Add_Pow_4.Ne_0.ferrari hβ h


-- created on 2018-11-27
-- updated on 2026-08-30
