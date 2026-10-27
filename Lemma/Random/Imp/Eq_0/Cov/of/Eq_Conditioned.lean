import Mathlib.Probability.Moments.Covariance
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory


/--
History-irrelevant coordinates are uncorrelated: distinct indices of a pairwise independent
family have covariance zero.
-/
@[path]
private lemma main
  [MeasurableSpace Ω] [DecidableEq ι]
  {π : Measure Ω}
  {x : ι → Ω → ℝ}
  {i j : ι}
-- given
  (h₀ : i ≠ j)
  (h₁ : x i ⟂ᵢ[π] x j)
  (h₂ : MemLp (x i) 2 π)
  (h₃ : MemLp (x j) 2 π) :
-- imply
  covariance (x i) (x j) π = 0 :=
-- proof
  if h : i = j then absurd h h₀ else h₁.covariance_eq_zero h₂ h₃


-- created on 2023-04-19
-- updated on 2026-10-26
