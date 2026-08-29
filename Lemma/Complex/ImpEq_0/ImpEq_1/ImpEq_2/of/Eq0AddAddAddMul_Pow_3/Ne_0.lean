import Lemma.Complex.ImpEq_0.ImpEq_1.ImpEq_2.of.Eq0AddAddAddPow_3
open Complex Nat


@[main]
private lemma main
  {x a b c d : ℂ}
-- given
  (ha : a ≠ 0)
  (h : a * x ^ 3 + b * x ^ 2 + c * x + d = 0) :
-- imply
  let a' : ℂ := b / a
  let b' : ℂ := c / a
  let c' : ℂ := d / a
  let p : ℂ := b' - a' ^ 2 / 3
  let q : ℂ := 2 * a' ^ 3 / 27 - a' * b' / 3 + c'
  let δ : ℂ := 4 * p ^ 3 / 27 + q ^ 2
  let U : ℂ := √δ - q
  let V : ℂ := -√δ - q
  let A : ℂ := (√δ / 2 - q / 2) ^ (3 : ℂ)⁻¹
  let B : ℂ := (-√δ / 2 - q / 2) ^ (3 : ℂ)⁻¹
  let ω : ℂ := (I * (2 * π / 3)).exp
  let D : ℤ :=
    ⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉ -
      ⌈3 * arg (U ^ (3 : ℂ)⁻¹ * V ^ (3 : ℂ)⁻¹) / (2 * π) - 1 / 2⌉
  x = A * ω ^ D + B - a' / 3 ∨
    x = A * ω ^ (D - 1) + B * ω - a' / 3 ∨
    x = A * ω ^ (D + 1) + B * ~ω - a' / 3 := by
-- proof
  intro a' b' c' p q δ U V A B ω D
  apply ImpEq_0.ImpEq_1.ImpEq_2.of.Eq0AddAddAddPow_3
  apply
    (OrEqS_0.of.Mul.eq.Zero
      (a := a)
      (b := x ^ 3 + a' * x ^ 2 + b' * x + c')
      ?_).resolve_left ha
  refine Eq.trans ?_ h
  simp only [a', b', c']
  field_simp [ha]


-- created on 2018-11-25
-- updated on 2026-08-29
