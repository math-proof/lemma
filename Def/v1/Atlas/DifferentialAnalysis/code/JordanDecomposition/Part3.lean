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
import Theorem.v1.Atlas.DifferentialAnalysis.code.JordanDecomposition.Part2


namespace ContinuousFunctions

open ContinuousLinearMap

section PosPartConstruction

variable {X : Type*} [MetricSpace X]

/-- The positive part of `u` evaluated at `f`: defined as `sup {u g | 0 ≤ g ≤ f}`. This is the
classical construction used to extract the positive component in the Jordan decomposition. -/
noncomputable def posPartSup (u : C₀Map X →L[ℝ] ℝ) (f : C₀Map X) : ℝ :=
  sSup (posPartSet u f)

end PosPartConstruction
end ContinuousFunctions
