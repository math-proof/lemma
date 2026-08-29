import Lemma.Complex.OrEqS.of.Eq0AddAddAddPow_4.EqModSubCeilSSubDivMul3Arg.Ne_0
import Lemma.Complex.OrEqS.of.Eq0AddAddAddPow_4.EqSubCeilSSubDivMul3Arg.Ne_0
open Complex


@[main]
private lemma main
  {x α β γ : ℂ}
-- given
  (hβ : β ≠ 0)
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
        ⌈3 * arg (U ^ (3 : ℂ)⁻¹ * V ^ (3 : ℂ)⁻¹) / (2 * π) - 1 / 2⌉
      )
  let ω : ℂ := (I * (2 * π / 3)).exp
  (D = 0 →
    let y : ℂ := A + B
    let y0 : ℂ := -2 * α / 3 + y
    let y1 : ℂ := 4 * α / 3 + y
    x = √(2 * β / √y0 - y1) / 2 - √y0 / 2 ∨
      x = -√(2 * β / √y0 - y1) / 2 - √y0 / 2 ∨
      x = √(-2 * β / √y0 - y1) / 2 + √y0 / 2 ∨
      x = -√(-2 * β / √y0 - y1) / 2 + √y0 / 2) ∧
    (D % 3 = 1 →
      let y : ℂ := A * ω + B
      let y0 : ℂ := -2 * α / 3 + y
      let y1 : ℂ := 4 * α / 3 + y
      x = √(2 * β / √y0 - y1) / 2 - √y0 / 2 ∨
        x = -√(2 * β / √y0 - y1) / 2 - √y0 / 2 ∨
        x = √(-2 * β / √y0 - y1) / 2 + √y0 / 2 ∨
        x = -√(-2 * β / √y0 - y1) / 2 + √y0 / 2) ∧
    (D % 3 = 2 →
      let y : ℂ := A * ~ω + B
      let y0 : ℂ := -2 * α / 3 + y
      let y1 : ℂ := 4 * α / 3 + y
      x = √(2 * β / √y0 - y1) / 2 - √y0 / 2 ∨
        x = -√(2 * β / √y0 - y1) / 2 - √y0 / 2 ∨
        x = √(-2 * β / √y0 - y1) / 2 + √y0 / 2 ∨
        x = -√(-2 * β / √y0 - y1) / 2 + √y0 / 2) := by
-- proof
  intro δ U V A B ar br cr p q δc D ω
  refine ⟨?_, ?_, ?_⟩
  ·
    intro hD y y0 y1
    apply OrEqS.of.Eq0AddAddAddPow_4.EqSubCeilSSubDivMul3Arg.Ne_0 (d := (0 : ℤ)) hβ
    ·
      convert hD
    ·
      apply h
  ·
    intro hD y y0 y1
    apply OrEqS.of.Eq0AddAddAddPow_4.EqModSubCeilSSubDivMul3Arg.Ne_0 (d := (1 : ℤ)) hβ
    ·
      convert hD
    ·
      apply h
  ·
    intro hD y y0 y1
    apply OrEqS.of.Eq0AddAddAddPow_4.EqModSubCeilSSubDivMul3Arg.Ne_0 (d := (2 : ℤ)) hβ
    ·
      convert hD
    ·
      apply h


-- created on 2018-11-27
-- updated on 2026-08-29
