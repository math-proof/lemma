/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/HormanderFundamental.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Distribution.Support
public import Def.v1.Atlas.DifferentialAnalysis.code.DifferentialOperators.Part2
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.DifferentialOperators
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.TemperedDistributions
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.SchwartzPartition
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.SmoothingOperators
public import Def.v1.Atlas.DifferentialAnalysis.code.TemperedDistributions
public import Theorem.v1.Atlas.DifferentialAnalysis.code.SchwartzPartition
public import Def.v1.Atlas.DifferentialAnalysis.code.SmoothingOperators
public import Theorem.v1.Atlas.DifferentialAnalysis.code.HormanderFundamental

@[expose] public section

open scoped SchwartzMap LineDeriv Pointwise Manifold
open Distribution


noncomputable section

namespace DifferentialOperators

variable {n : ℕ}


/-- The Schwartz function `y ↦ φ(x − y)` obtained by translating and reflecting a Schwartz function `φ` by `x`. -/
def schwartzTranslateReflect
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (x : EuclideanSpace ℝ (Fin n)) :
    𝓢(EuclideanSpace ℝ (Fin n), ℂ) where
  toFun := fun y => φ (x - y)
  smooth' := φ.smooth'.comp (contDiff_const.sub contDiff_id)
  decay' := schwartzTranslateReflect_decay φ x

/-- Convolution of a tempered distribution `u` with a Schwartz function `φ`: pointwise `(u ∗ φ)(x) = ⟨u, φ(x − ·)⟩`. -/
def temperedConvolution
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    EuclideanSpace ℝ (Fin n) → ℂ :=
  fun x => u (schwartzTranslateReflect φ x)

end DifferentialOperators
end
