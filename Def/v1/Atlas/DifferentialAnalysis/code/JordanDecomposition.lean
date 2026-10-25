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
import Abbrev.v1.Atlas.DifferentialAnalysis.code.JordanDecomposition


namespace ContinuousFunctions

/-- A continuous linear functional `u` on `C₀(X, ℝ)` is positive iff it sends nonnegative
functions to nonnegative real numbers. -/
def IsPositiveFunctional {X : Type*} [TopologicalSpace X]
    (u : C₀Map X →L[ℝ] ℝ) : Prop :=
  ∀ f : C₀Map X, (∀ x, 0 ≤ f x) → 0 ≤ u f

end ContinuousFunctions
