module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter4.Thm_4_6
public import Theorem.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter4.Thm_4_6
public import Theorem.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter4.Cor_4_9
public import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter4.Cor_4_9
public import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter4.EuclideanBridge
open MeasureTheory ProbabilityTheory Matrix Real Finset BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/EuclideanBridge.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

set_option linter.unusedVariables false

set_option maxHeartbeats 800000

variable {d : ℕ}

namespace EuclideanBridge

/-- `euclideanToFun` left-inverts `funToEuclidean`. -/
@[simp] lemma euclideanToFun_funToEuclidean (v : Fin d → ℝ) :
    euclideanToFun (funToEuclidean v) = v :=
  (WithLp.equiv 2 (Fin d → ℝ)).apply_symm_apply v

/-- `funToEuclidean` left-inverts `euclideanToFun`. -/
@[simp] lemma funToEuclidean_euclideanToFun (v : EuclideanSpace ℝ (Fin d)) :
    funToEuclidean (euclideanToFun v) = v :=
  (WithLp.equiv 2 (Fin d → ℝ)).symm_apply_apply v

/-- Componentwise, `euclideanToFun` is the identity. -/
@[simp] lemma euclideanToFun_apply (v : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    euclideanToFun v i = v i := rfl

/-- Componentwise, `funToEuclidean` is the identity. -/
@[simp] lemma funToEuclidean_apply (v : Fin d → ℝ) (i : Fin d) :
    funToEuclidean v i = v i := rfl

end EuclideanBridge
end
