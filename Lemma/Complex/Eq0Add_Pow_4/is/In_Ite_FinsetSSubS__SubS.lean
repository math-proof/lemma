import Lemma.Complex.Eq0Add_Pow_4.is.In_Ite_FinsetS
import Lemma.Set.In_Finset.is.Or_OrEqS
import Lemma.Set.In_Insert.is.Eq.ou.In
open Complex Set


/--
| attributes | lemma |
| :---: | :---: |
| main | Complex.Eq0Add_Pow_4.is.In_Ite_FinsetSSubS__SubS |
| comm | Complex.In_Ite_FinsetSSubS__SubS.is.Eq0Add_Pow_4 |
| mp | Complex.In_Ite_FinsetSSubS__SubS.of.Eq0Add_Pow_4 |
| mpr | Complex.Eq0Add_Pow_4.of.In_Ite_FinsetSSubS__SubS |
-/
@[main, comm, mp, mpr]
private lemma main
  {x a b c d : ℂ} :
-- imply
  d + c * x + b * x ^ 2 + a * x ^ 3 + x ^ 4 = 0 ↔
    let α := b - 3 * a ^ 2 / 8
    let β := a ^ 3 / 8 + c - a * b / 2
    let γ := a ^ 2 * b / 16 + d - 3 * a ^ 4 / 256 - a * c / 4
    x ∈ (if β = 0 then
      let Δ := α ^ 2 - 4 * γ
      ({√((√Δ - α) / 2) - a / 4, √((-√Δ - α) / 2) - a / 4, -√((√Δ - α) / 2) - a / 4, -√((-√Δ - α) / 2) - a / 4} : Set ℂ)
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
      ({(√(2 * β / √y₀ - y₁) - √y₀) / 2 - a / 4, (-√(2 * β / √y₀ - y₁) - √y₀) / 2 - a / 4, (√(-2 * β / √y₀ - y₁) + √y₀) / 2 - a / 4, (-√(-2 * β / √y₀ - y₁) + √y₀) / 2 - a / 4} : Set ℂ)) := by
-- proof
  extract_lets α β γ
  let z := x + a / 4
  rw [(by grind : d + c * x + b * x ^ 2 + a * x ^ 3 + x ^ 4 = γ + β * z + α * z ^ 2 + z ^ 4)]
  rw [Eq0Add_Pow_4.is.In_Ite_FinsetS]
  have hlin (r : ℂ) : x + a / 4 = r ↔ x = r - a / 4 := by grind
  grind


-- created on 2018-11-28
-- updated on 2026-09-01
