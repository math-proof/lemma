import sympy.core.power
import sympy.polys.polyroots
import Lemma.Algebra.Or_Eq.of.Add.eq.Zero.biquadratic
open Algebra


@[main]
private lemma main
  {x α β γ : ℂ}
-- given
  (h : x ^ 4 + α * x ^ 2 + β * x + γ = 0) :
-- imply
  (β = 0 →
    let Δ : ℂ := α ^ 2 - 4 * γ
    x = √(√Δ / 2 - α / 2) ∨
      x = -√(√Δ / 2 - α / 2) ∨
      x = √(-√Δ / 2 - α / 2) ∨
      x = -√(-√Δ / 2 - α / 2)) := by
-- proof
  intro hβ Δ
  have hbq : x ^ 4 + α * x ^ 2 + γ = 0 := by
    simpa [hβ] using h
  simpa [Δ] using Or_Eq.of.Add.eq.Zero.biquadratic hbq


-- created on 2018-11-27
-- updated on 2026-08-20
