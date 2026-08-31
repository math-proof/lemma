import Lemma.Complex.Eq0Add_Pow_4.is.In_FinsetSqrtS_NegSSqrt
import Lemma.Complex.Eq0Add_Pow_4.is.In_FinsetDivS_2DivS_2.of.Ne_0
open Complex


/--
| attributes | lemma |
| :---: | :---: |
| main | Complex.Eq0Add_Pow_4.is.In_Ite_FinsetS |
| comm | Complex.In_Ite_FinsetS.is.Eq0Add_Pow_4 |
| mp | Complex.In_Ite_FinsetS.of.Eq0Add_Pow_4 |
| mpr | Complex.Eq0Add_Pow_4.of.In_Ite_FinsetS |
-/
@[main, comm, mp, mpr]
private lemma main
  {x α β γ : ℂ} :
-- imply
  γ + β * x + α * x ^ 2 + x ^ 4 = 0 ↔
    x ∈ (if β = 0 then
      let Δ := α ^ 2 - 4 * γ
      ({√((√Δ - α) / 2), √((-√Δ - α) / 2), -√((√Δ - α) / 2), -√((-√Δ - α) / 2)} : Set ℂ)
    else
      let p := -4 * γ - α ^ 2 / 3
      let q := -2 * α ^ 3 / 27 + 8 * α * γ / 3 - β ^ 2
      let δ := 4 * p ^ 3 / 27 + q ^ 2
      let A := ∛((-q + √δ) / 2)
      let B := ∛((-q - √δ) / 2)
      let k := ⌈3 * arg (-p) / (2 * π) - 1 / 2⌉ - ⌈3 * arg (A * B) / (2 * π) - 1 / 2⌉
      let ω := (I * (2 * π / 3)).exp
      let y := A * ω ^ k + B
      let y₀ := -2 * α / 3 + y
      let y₁ := 4 * α / 3 + y
      ({(√(2 * β / √y₀ - y₁) - √y₀) / 2, (-√(2 * β / √y₀ - y₁) - √y₀) / 2, (√(-2 * β / √y₀ - y₁) + √y₀) / 2, (-√(-2 * β / √y₀ - y₁) + √y₀) / 2} : Set ℂ)) := by
-- proof
  split_ifs with hβ
  ·
    rw [hβ]
    rw [(by ring : γ + 0 * x + α * x ^ 2 + x ^ 4 = γ + α * x ^ 2 + x ^ 4), Eq0Add_Pow_4.is.In_FinsetSqrtS_NegSSqrt]
  ·
    rw [Eq0Add_Pow_4.is.In_FinsetDivS_2DivS_2.of.Ne_0 hβ]


-- created on 2018-11-27
-- updated on 2026-08-31
