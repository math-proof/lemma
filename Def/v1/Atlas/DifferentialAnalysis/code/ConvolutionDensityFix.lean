/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConvolutionDensityFix.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.DifferentialAnalysis.code.TestFunctions
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.TestFunctions
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
open TestFunctions
open scoped ZeroAtInfty
open Filter Topology Metric


noncomputable section

namespace ConvolutionDensity

/-- The predicate `allPdBound k f δ` asserts that all partial derivatives of
`f` of order `≤ k` (taken with respect to standard basis directions) are
bounded by `δ` in norm.  Defined recursively in `k`. -/
def allPdBound {n : ℕ} : ℕ → (EuclideanSpace ℝ (Fin n) → ℂ) → ℝ → Prop
  | 0, f, δ => ∀ x, ‖f x‖ ≤ δ
  | k + 1, f, δ => allPdBound k f δ ∧
      ∀ j : Fin n, allPdBound k (fun x => fderiv ℝ f x (EuclideanSpace.single j 1)) δ

end ConvolutionDensity
end
