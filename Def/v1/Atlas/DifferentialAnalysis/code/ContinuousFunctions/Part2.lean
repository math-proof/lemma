/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ContinuousFunctions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Lipschitz
import Theorem.v1.Atlas.DifferentialAnalysis.code.ContinuousFunctions
open Set Filter Topology
open scoped ZeroAtInfty


namespace ContinuousFunctions

/-- Two norms on `V` are equivalent if they are mutually controlled by a single positive
constant, i.e. `(1/C) · norm₁ v ≤ norm₂ v ≤ C · norm₁ v` for all `v`. -/
def AreEquivalentNorms {V : Type*} (norm₁ norm₂ : V → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ v : V, (1 / C) * norm₁ v ≤ norm₂ v ∧ norm₂ v ≤ C * norm₁ v

end ContinuousFunctions
