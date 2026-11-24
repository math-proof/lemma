module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Theorem.Analysis.InnerProductSpace.DiscreteSpectrum.Part4
open scoped BigOperators


public section

/--
[DiscreteSpectrum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/DiscreteSpectrum.lean)
-/
@[path]
private theorem riesz_mean_zero_eq
-- given
  (S : NonnegativeDiscreteSpectrum)
  (Λ : ℝ) :
-- imply
  S.rieszMean 0 Λ = S.countingFunction Λ := by
-- proof
  apply NonnegativeDiscreteSpectrum.rieszMean_zero S Λ

-- created on 2026-10-10
-- updated on 2026-10-26
