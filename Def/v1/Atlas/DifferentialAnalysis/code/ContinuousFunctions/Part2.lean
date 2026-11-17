/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ContinuousFunctions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.PartitionOfUnity
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Algebra.Order.Group.MinMax
public import Mathlib.Topology.Sequences
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Theorem.v1.Atlas.DifferentialAnalysis.code.ContinuousFunctions

@[expose] public section

open Set Filter Topology
open scoped ZeroAtInfty


namespace ContinuousFunctions

/-- Two norms on `V` are equivalent if they are mutually controlled by a single positive
constant, i.e. `(1/C) · norm₁ v ≤ norm₂ v ≤ C · norm₁ v` for all `v`. -/
def AreEquivalentNorms {V : Type*} (norm₁ norm₂ : V → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ v : V, (1 / C) * norm₁ v ≤ norm₂ v ∧ norm₂ v ≤ C * norm₁ v

end ContinuousFunctions
