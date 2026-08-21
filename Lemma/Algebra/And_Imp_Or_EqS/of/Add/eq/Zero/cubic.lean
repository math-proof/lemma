import sympy.core.power
import sympy.core.numbers
import sympy.polys.polyroots
import Lemma.Algebra.And_Imp_Or_EqS_Div.of.Add.eq.Zero.quadratic
import Lemma.Algebra.And.Imp.Or.Eq.of.Add.eq.Zero.cubic.one_leaded
open Algebra


@[main]
private lemma main
  {x a b c d : ℂ}
-- given
  (h : a * x ^ 3 + b * x ^ 2 + c * x + d = 0) :
-- imply
  (a = 0 ∧ b = 0 ∧ c = 0 → d = 0) ∧
    (a = 0 ∧ b = 0 ∧ c ≠ 0 → x = -d / c) ∧
    (a = 0 ∧ b ≠ 0 →
      let Δ : ℂ := c ^ 2 - 4 * b * d
      x = (-c + √Δ) / (2 * b) ∨ x = (-c - √Δ) / (2 * b)) ∧
    (a ≠ 0 →
      let a' : ℂ := b / a
      let b' : ℂ := c / a
      let c' : ℂ := d / a
      let p : ℂ := b' - a' ^ 2 / 3
      let q : ℂ := 2 * a' ^ 3 / 27 - a' * b' / 3 + c'
      let δ : ℂ := 4 * p ^ 3 / 27 + q ^ 2
      let A : ℂ := (√δ / 2 - q / 2) ^ (3 : ℂ)⁻¹
      let B : ℂ := (-√δ / 2 - q / 2) ^ (3 : ℂ)⁻¹
      let D : ℤ :=
        ⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉ -
          ⌈3 * arg (A * B) / (2 * π) - 1 / 2⌉
      let ω : ℂ := ↑(-(1 / 2 : ℝ)) + ↑(√3 / 2 : ℝ) * I
      (D = 0 →
          x = A + B - a' / 3 ∨
            x = A * ω + B * (starRingEnd ℂ) ω - a' / 3 ∨
            x = A * (starRingEnd ℂ) ω + B * ω - a' / 3) ∧
        (D % 3 = 1 →
          x = A * ω + B - a' / 3 ∨
            x = A * (starRingEnd ℂ) ω + B * (starRingEnd ℂ) ω - a' / 3 ∨
            x = A + B * ω - a' / 3) ∧
        (D % 3 = 2 →
          x = A * (starRingEnd ℂ) ω + B - a' / 3 ∨
            x = A + B * (starRingEnd ℂ) ω - a' / 3 ∨
            x = A * ω + B * ω - a' / 3)) := by
-- proof
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro ⟨ha, hb, hc⟩
    simpa [ha, hb, hc] using h
  ·
    intro ⟨ha, hb, hc⟩
    have hq := And_Imp_Or_EqS_Div.of.Add.eq.Zero.quadratic
      (x := x) (a := (0 : ℂ)) (b := c) (c := d) (by simpa [ha, hb] using h)
    exact hq.2.1 ⟨rfl, hc⟩
  ·
    intro ⟨ha, hb⟩
    have hq := And_Imp_Or_EqS_Div.of.Add.eq.Zero.quadratic
      (x := x) (a := b) (b := c) (c := d) (by simpa [ha] using h)
    simpa using hq.2.2 hb
  ·
    intro ha a' b' c' p q δ A B D ω
    have hmonic : x ^ 3 + a' * x ^ 2 + b' * x + c' = 0 := by
      have hmul :
          a * (x ^ 3 + (b / a) * x ^ 2 + (c / a) * x + d / a) =
            a * x ^ 3 + b * x ^ 2 + c * x + d := by
        field_simp [ha]
      have h0 : a * (x ^ 3 + a' * x ^ 2 + b' * x + c') = 0 := by
        simp only [a', b', c']
        rw [hmul, h]
      exact (mul_eq_zero.mp h0).resolve_left ha
    exact And.Imp.Or.Eq.of.Add.eq.Zero.cubic.one_leaded hmonic


-- created on 2018-11-25
-- updated on 2026-08-20
