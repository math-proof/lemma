import Lemma.Complex.Imp_OrOrSEqS_Sub.Imp_OrOrSEqS_SubDiv_2.of.Eq0Add_Pow_4
import Lemma.Nat.Mul.eq.Zero.is.OrEqS_0
open Complex Nat


@[main]
private lemma main
  {x a b c d e : ℂ}
-- given
  (ha : a ≠ 0)
  (h : e + d * x + c * x ^ 2 + b * x ^ 3 + a * x ^ 4 = 0) :
-- imply
  let a' := b / a
  let b' := c / a
  let c' := d / a
  let d' := e / a
  let α := b' - 3 * a' ^ 2 / 8
  let β := a' ^ 3 / 8 + c' - a' * b' / 2
  let γ := a' ^ 2 * b' / 16 + d' - 3 * a' ^ 4 / 256 - a' * c' / 4
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
  (β = 0 →
    let Δ := α ^ 2 - 4 * γ
    (x = √((√Δ - α) / 2) - a' / 4 ∨
      x = -√((√Δ - α) / 2) - a' / 4) ∨
      x = √((-√Δ - α) / 2) - a' / 4 ∨
      x = -√((-√Δ - α) / 2) - a' / 4) ∧
    (β ≠ 0 →
      (x = (√(2 * β / √y0 - y1) - √y0) / 2 - a' / 4 ∨
        x = (-√(2 * β / √y0 - y1) - √y0) / 2 - a' / 4) ∨
        x = (√(-2 * β / √y0 - y1) + √y0) / 2 - a' / 4 ∨
        x = (-√(-2 * β / √y0 - y1) + √y0) / 2 - a' / 4) := by
-- proof
  intro a' b' c' d' α β γ p q δ A B k ω y y0 y1
  apply Imp_OrOrSEqS_Sub.Imp_OrOrSEqS_SubDiv_2.of.Eq0Add_Pow_4
  apply (OrEqS_0.of.Mul.eq.Zero (a := a) (b := d' + c' * x + b' * x ^ 2 + a' * x ^ 3 + x ^ 4) ?_).resolve_left ha
  refine Eq.trans ?_ h
  simp only [a', b', c', d']
  field_simp [ha]


-- created on 2018-11-29
-- updated on 2026-08-30
