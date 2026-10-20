import Mathlib.Probability.Moments.Covariance
import sympy.Basic
open MeasureTheory ProbabilityTheory


/--
If the past index `i` is strictly before `t`, pairwise independence gives `cov[x i, x t] = 0`.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω}
  {x : ℕ → Ω → ℝ}
  {i t : ℕ}
-- given
  (h₀ : i < t)
  (h₁ : x i ⟂ᵢ[π] x t)
  (h₂ : MemLp (x i) 2 π)
  (h₃ : MemLp (x t) 2 π) :
-- imply
  covariance (x i) (x t) π = 0 :=
-- proof
  if h : i = t then absurd h h₀.ne else h₁.covariance_eq_zero h₂ h₃


-- created on 2023-04-19
-- updated on 2026-10-17
