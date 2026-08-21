import sympy.core.power
import sympy.core.numbers
import sympy.polys.polyroots
import Lemma.Algebra.And.Imp.of.Add.eq.Zero.quartic.depressed
open Algebra


@[main]
private lemma main
  {x a b c d : ℂ}
-- given
  (h : x ^ 4 + a * x ^ 3 + b * x ^ 2 + c * x + d = 0) :
-- imply
  let α : ℂ := b - 3 * a ^ 2 / 8
  let β : ℂ := a ^ 3 / 8 + c - a * b / 2
  let γ : ℂ := a ^ 2 * b / 16 + d - 3 * a ^ 4 / 256 - a * c / 4
  (β = 0 →
    let Δ : ℂ := α ^ 2 - 4 * γ
    x = √(√Δ / 2 - α / 2) - a / 4 ∨
      x = -√(√Δ / 2 - α / 2) - a / 4 ∨
      x = √(-√Δ / 2 - α / 2) - a / 4 ∨
      x = -√(-√Δ / 2 - α / 2) - a / 4) := by
-- proof
  intro α β γ hβ Δ
  let z : ℂ := x + a / 4
  have hx : x = z - a / 4 := by
    simp [z]
  have hz : z ^ 4 + α * z ^ 2 + β * z + γ = 0 := by
    rw [hx] at h
    simp only [α, β, γ] at h ⊢
    convert h using 1
    ring
  have hdep := And.Imp.of.Add.eq.Zero.quartic.depressed (by simpa [hβ] using hz) hβ
  rcases hdep with hz' | hz' | hz' | hz'
  ·
    exact Or.inl (eq_sub_of_add_eq hz')
  ·
    exact Or.inr (Or.inl (eq_sub_of_add_eq hz'))
  ·
    exact Or.inr (Or.inr (Or.inl (eq_sub_of_add_eq hz')))
  ·
    exact Or.inr (Or.inr (Or.inr (eq_sub_of_add_eq hz')))


-- created on 2018-11-28
-- updated on 2026-08-21
