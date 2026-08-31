import Lemma.Complex.Eq0Add_Pow_4.is.In_Ite_FinsetSSubS__SubS
open Complex


/--
| attributes | lemma |
| :---: | :---: |
| main | Complex.Eq0Add_Mul_Pow_4.is.In_Ite_FinsetSSubS__SubS.of.Ne_0 |
| comm | Complex.In_Ite_FinsetSSubS__SubS.is.Eq0Add_Mul_Pow_4.of.Ne_0 |
| mp | Complex.In_Ite_FinsetSSubS__SubS.of.Eq0Add_Mul_Pow_4.Ne_0 |
| mpr | Complex.Eq0Add_Mul_Pow_4.of.In_Ite_FinsetSSubS__SubS.Ne_0 |
-/
@[main, comm, mp, mpr]
private lemma main
  {x a b c d e : ℂ}
-- given
  (ha : a ≠ 0) :
-- imply
  e + d * x + c * x ^ 2 + b * x ^ 3 + a * x ^ 4 = 0 ↔
    let a' := b / a
    let b' := c / a
    let c' := d / a
    let d' := e / a
    let α := b' - 3 * a' ^ 2 / 8
    let β := a' ^ 3 / 8 + c' - a' * b' / 2
    let γ := a' ^ 2 * b' / 16 + d' - 3 * a' ^ 4 / 256 - a' * c' / 4
    x ∈ (if β = 0 then
      let Δ := α ^ 2 - 4 * γ
      ({√((√Δ - α) / 2) - a' / 4, √((-√Δ - α) / 2) - a' / 4, -√((√Δ - α) / 2) - a' / 4, -√((-√Δ - α) / 2) - a' / 4} : Set ℂ)
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
      ({(√(2 * β / √y₀ - y₁) - √y₀) / 2 - a' / 4, (-√(2 * β / √y₀ - y₁) - √y₀) / 2 - a' / 4, (√(-2 * β / √y₀ - y₁) + √y₀) / 2 - a' / 4, (-√(-2 * β / √y₀ - y₁) + √y₀) / 2 - a' / 4} : Set ℂ)) :=
-- proof
  Iff.trans (by grind) Eq0Add_Pow_4.is.In_Ite_FinsetSSubS__SubS


-- created on 2018-11-29
-- updated on 2026-09-01
