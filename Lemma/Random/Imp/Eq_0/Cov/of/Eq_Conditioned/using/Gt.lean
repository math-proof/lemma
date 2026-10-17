import Mathlib.Probability.Moments.Covariance
import sympy.Basic
open MeasureTheory ProbabilityTheory


/--
If the time index `t` is strictly after `i`, pairwise independence gives `cov[x t, x i] = 0`.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω}
  {x : ℕ → Ω → ℝ}
  {i t : ℕ}
-- given
  (h₀ : t > i)
  (h₁ : x t ⟂ᵢ[π] x i)
  (h₂ : MemLp (x t) 2 π)
  (h₃ : MemLp (x i) 2 π) :
-- imply
  covariance (x t) (x i) π = 0 :=
-- proof
  if h : t = i then absurd h h₀.ne.symm else h₁.covariance_eq_zero h₂ h₃


-- created on 2026-10-11
-- updated on 2026-10-17
