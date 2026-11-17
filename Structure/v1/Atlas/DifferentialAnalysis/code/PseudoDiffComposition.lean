/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/PseudoDiffComposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.MeanValue
public import Def.v1.Atlas.DifferentialAnalysis.code.DifferentialOperators.Part2
public import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.DifferentialOperators
public import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.LaplacianExistence


public noncomputable section

open scoped SchwartzMap

open Filter Topology MeasureTheory

namespace PoissonEquation

variable (n : ℕ)

/-- A smooth `ℂ`-valued function on `ℝⁿ` whose iterated derivatives of every order decay to zero at infinity (i.e. tend to `0` along the cocompact filter). -/
structure SmoothZeroAtInfty where
  toFun : EuclideanSpace ℝ (Fin n) → ℂ
  smooth' : ContDiff ℝ (⊤ : ℕ∞) toFun
  zero_at_infty' : ∀ m : ℕ,
    Tendsto (fun x => ‖iteratedFDeriv ℝ m toFun x‖) (cocompact _) (𝓝 0)

end PoissonEquation
end
