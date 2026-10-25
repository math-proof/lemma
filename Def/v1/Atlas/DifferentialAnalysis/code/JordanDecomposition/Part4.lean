/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/JordanDecomposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.DifferentialAnalysis.code.ContinuousFunctions.Part2
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.ContinuousFunctions
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
import Theorem.v1.Atlas.DifferentialAnalysis.code.JordanDecomposition.Part3


namespace ContinuousFunctions

open ContinuousLinearMap

section PosPartConstruction

variable {X : Type*} [MetricSpace X]

/-- The positive-part functional extended to arbitrary (signed) `C₀` functions via the
decomposition `f = f⁺ - f⁻`. -/
noncomputable def posPartFn (u : C₀Map X →L[ℝ] ℝ) (f : C₀Map X) : ℝ :=
  posPartSup u (zeroAtInftyPosPart f) - posPartSup u (zeroAtInftyNegPart f)

end PosPartConstruction
end ContinuousFunctions
