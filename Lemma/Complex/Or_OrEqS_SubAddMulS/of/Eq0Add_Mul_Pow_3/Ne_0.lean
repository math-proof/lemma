import Lemma.Complex.Or_OrEqS_SubAddMulS.of.Eq0Add_Pow_3
open Complex


@[main]
private lemma main
  {x a b c d : ℂ}
-- given
  (ha : a ≠ 0)
  (h : d + c * x + b * x ^ 2 + a * x ^ 3 = 0) :
-- imply
  let a' : ℂ := b / a
  let b' : ℂ := c / a
  let c' : ℂ := d / a
  let p : ℂ := b' - a' ^ 2 / 3
  let q : ℂ := 2 * a' ^ 3 / 27 - a' * b' / 3 + c'
  let δ : ℂ := 4 * p ^ 3 / 27 + q ^ 2
  let A : ℂ := ∛((-q + √δ) / 2)
  let B : ℂ := ∛((-q - √δ) / 2)
  let ω : ℂ := (I * (2 * π / 3)).exp
  let k : ℤ := ⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉ - ⌈3 * arg (A * B) / (2 * π) - 1 / 2⌉
  x = A * ω ^ k + B - a' / 3 ∨
    x = A * ω ^ (k - 1) + B * ω - a' / 3 ∨
    x = A * ω ^ (k + 1) + B * ~ω - a' / 3 := by
-- proof
  intro a' b' c' p q δ A B ω k
  apply Or_OrEqS_SubAddMulS.of.Eq0Add_Pow_3
  apply (Nat.OrEqS_0.of.Mul.eq.Zero (a := a) (b := c' + b' * x + a' * x ^ 2 + x ^ 3) ?_).resolve_left ha
  refine Eq.trans ?_ h
  simp only [a', b', c']
  field_simp [ha]


-- created on 2018-11-25
-- updated on 2026-08-29
