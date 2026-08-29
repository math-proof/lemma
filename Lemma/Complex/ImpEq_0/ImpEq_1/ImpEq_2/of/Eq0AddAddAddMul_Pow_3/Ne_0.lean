import sympy.core.power
import sympy.core.numbers
import sympy.functions.elementary.complexes
import sympy.polys.polyroots
import Lemma.Complex.ImpEq_0.ImpEq_1.ImpEq_2.of.Eq0AddAddAddPow_3
open Complex


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
  let ω : ℂ := ↑(-(1 / 2 : ℝ)) + ↑(√3 / 2 : ℝ) * I
  let D : ℤ :=
    ⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉ -
      ⌈3 * arg (U ^ (3 : ℂ)⁻¹ * V ^ (3 : ℂ)⁻¹) / (2 * π) - 1 / 2⌉
  (D = 0 →
      x = A + B - a' / 3 ∨
        x = A * ω + B * ~ω - a' / 3 ∨
        x = A * ~ω + B * ω - a' / 3) ∧
    (D % 3 = 1 →
      x = A * ω + B - a' / 3 ∨
        x = A * ~ω + B * ~ω - a' / 3 ∨
        x = A + B * ω - a' / 3) ∧
    (D % 3 = 2 →
      x = A * ~ω + B - a' / 3 ∨
        x = A + B * ~ω - a' / 3 ∨
        x = A * ω + B * ω - a' / 3) := by
-- proof
  intro a' b' c' p q δ U V A B ω D
  have hmonic : x ^ 3 + a' * x ^ 2 + b' * x + c' = 0 := by
    have hmul :
        a * (x ^ 3 + (b / a) * x ^ 2 + (c / a) * x + d / a) =
          a * x ^ 3 + b * x ^ 2 + c * x + d := by
      field_simp [ha]
    have h0 : a * (x ^ 3 + a' * x ^ 2 + b' * x + c') = 0 := by
      simp only [a', b', c']
      rw [hmul, h]
    exact (mul_eq_zero.mp h0).resolve_left ha
  exact ImpEq_0.ImpEq_1.ImpEq_2.of.Eq0AddAddAddPow_3 hmonic


-- created on 2018-11-25
-- updated on 2026-08-29
