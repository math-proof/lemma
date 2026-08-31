import Lemma.Complex.In_Finset_SubSAddMulS.of.Eq0Add_Pow_3
import Lemma.Set.In_Finset.is.Or_OrEqS
open Complex Set


@[main]
private lemma main
  {x a b c d : ℂ}
-- given
  (ha : a ≠ 0)
  (h : d + c * x + b * x ^ 2 + a * x ^ 3 = 0) :
-- imply
  let a' := b / a
  let b' := c / a
  let c' := d / a
  let p := b' - a' ^ 2 / 3
  let q := 2 * a' ^ 3 / 27 - a' * b' / 3 + c'
  let δ := 4 * p ^ 3 / 27 + q ^ 2
  let A := ∛((-q + √δ) / 2)
  let B := ∛((-q - √δ) / 2)
  let ω := (I * (2 * π / 3)).exp
  let k := ⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉ - ⌈3 * arg (A * B) / (2 * π) - 1 / 2⌉
  x = A * ω ^ k + B - a' / 3 ∨
    x = A * ω ^ (k - 1) + B * ω - a' / 3 ∨
    x = A * ω ^ (k + 1) + B * ~ω - a' / 3 := by
-- proof
  intro a' b' c' p q δ A B ω k
  apply Or_OrEqS.of.In_Finset
  apply In_Finset_SubSAddMulS.of.Eq0Add_Pow_3
  apply (Nat.OrEqS_0.of.Mul.eq.Zero (a := a) (b := c' + b' * x + a' * x ^ 2 + x ^ 3) ?_).resolve_left ha
  refine Eq.trans ?_ h
  simp only [a', b', c']
  field_simp [ha]


-- created on 2018-11-25
-- updated on 2026-08-29
