import Lemma.Complex.Imp_OrOrSEqS.Imp_OrOrSEqS_Div_2.of.Eq0Add_Pow_4
open Complex


@[main]
private lemma main
  {x a b c d : ℂ}
-- given
  (h : d + c * x + b * x ^ 2 + a * x ^ 3 + x ^ 4 = 0) :
-- imply
  let α := b - 3 * a ^ 2 / 8
  let β := a ^ 3 / 8 + c - a * b / 2
  let γ := a ^ 2 * b / 16 + d - 3 * a ^ 4 / 256 - a * c / 4
  let p := -4 * γ - α ^ 2 / 3
  let q := -2 * α ^ 3 / 27 + 8 * α * γ / 3 - β ^ 2
  let δ := 4 * p ^ 3 / 27 + q ^ 2
  let A := ∛((-q + √δ) / 2)
  let B := ∛((-q - √δ) / 2)
  let k := ⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉ - ⌈3 * arg (A * B) / (2 * π) - 1 / 2⌉
  let ω := (I * (2 * π / 3)).exp
  let y := A * ω ^ k + B
  let y0 := -2 * α / 3 + y
  let y1 := 4 * α / 3 + y
  (β = 0 →
    let Δ := α ^ 2 - 4 * γ
    (x = √((√Δ - α) / 2) - a / 4 ∨
      x = -√((√Δ - α) / 2) - a / 4) ∨
      x = √((-√Δ - α) / 2) - a / 4 ∨
      x = -√((-√Δ - α) / 2) - a / 4) ∧
    (β ≠ 0 →
      (x = (√(2 * β / √y0 - y1) - √y0) / 2 - a / 4 ∨
        x = (-√(2 * β / √y0 - y1) - √y0) / 2 - a / 4) ∨
        x = (√(-2 * β / √y0 - y1) + √y0) / 2 - a / 4 ∨
        x = (-√(-2 * β / √y0 - y1) + √y0) / 2 - a / 4) := by
-- proof
  intro α β γ p q δ A B k ω y y0 y1
  let z := x + a / 4
  have hx : x = z - a / 4 := by
    simp [z]
  have hz : γ + β * z + α * z ^ 2 + z ^ 4 = 0 := by
    rw [hx] at h
    simp only [α, β, γ] at h ⊢
    convert h using 1
    ring
  refine ⟨?_, ?_⟩
  ·
    intro hβ Δ
    have hfour := (Imp_OrOrSEqS.Imp_OrOrSEqS_Div_2.of.Eq0Add_Pow_4 hz).1 hβ
    obtain (hz' | hz') | hz' | hz' := hfour <;> grind
  ·
    intro hβ
    have hfour := (Imp_OrOrSEqS.Imp_OrOrSEqS_Div_2.of.Eq0Add_Pow_4 hz).2 hβ
    obtain (hz' | hz') | hz' | hz' := hfour <;> grind


-- created on 2018-11-28
-- updated on 2026-08-30
