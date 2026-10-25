import Mathlib
import sympy.Basic
import Instance.v1.Atlas.FourierAnalysis.code.FourierSeries
open Real TorusConvolution ApproximateIdentity FejerL1Density


/--
[mulℂ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/FourierSeries.lean)
-/
@[path]
private lemma mulℂ_eq :
-- imply
  mulℂ = ContinuousLinearMap.mul ℂ ℂ :=
-- proof
  rfl

/--
[ApproximateIdentity.periodicConvolution](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/FourierSeries.lean)
-/
@[path]
private lemma ApproximateIdentity.periodicConvolution_eq
  {f K : ℝ → ℝ}
  {x : ℝ} :
-- imply
  ApproximateIdentity.periodicConvolution f K x =
    (1 / (2 * π)) * ∫ y in (-π)..π, f (x - y) * K y :=
-- proof
  rfl

/--
[FejerL1Density.periodicL1Norm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/FourierSeries.lean)
-/
@[path]
private lemma periodicL1Norm_eq
  {f : ℝ → ℝ} :
-- imply
  periodicL1Norm f = (1 / (2 * π)) * ∫ x in (-π)..π, |f x| :=
-- proof
  rfl

/--
[FejerL1Density.periodicConvolution](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/FourierSeries.lean)
-/
@[path]
private lemma FejerL1Density.periodicConvolution_eq
  {f K : ℝ → ℝ}
  {x : ℝ} :
-- imply
  FejerL1Density.periodicConvolution f K x =
    (1 / (2 * π)) * ∫ y in (-π)..π, f (x - y) * K y :=
-- proof
  rfl

/--
[fejerKernel](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/FourierSeries.lean)
-/
@[path]
private lemma fejerKernel_zero
  {x : ℝ} :
-- imply
  fejerKernel 0 x = 0 := by
-- proof
  simp [fejerKernel]

/--
[fejerMean](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/FourierSeries.lean)
-/
@[path]
private lemma fejerMean_eq
  {f : ℝ → ℝ}
  {N : ℕ} :
-- imply
  fejerMean f N = FejerL1Density.periodicConvolution f (fejerKernel N) :=
-- proof
  rfl

/--
[IsTrigPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/FourierSeries.lean)
-/
@[path]
private lemma IsTrigPolynomial_iff
  {p : ℝ → ℝ} :
-- imply
  IsTrigPolynomial p ↔
    ∃ (N : ℕ) (a b : ℕ → ℝ),
      ∀ x, p x = ∑ n ∈ Finset.range (N + 1),
        (a n * cos (n * x) + b n * sin (n * x)) :=
-- proof
  Iff.rfl


-- created on 2026-10-23
-- updated on 2026-10-24
