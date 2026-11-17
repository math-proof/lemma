/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/POUSeqDensityHelpers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Metrizable.Urysohn
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Compact
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.Module.WeakDual
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.PartitionOfUnity

@[expose] public section

set_option linter.unusedSectionVars false

open TopologicalSpace Metric Set Filter Topology


noncomputable section

section MetrizableLCSC

variable (X : Type*) [TopologicalSpace X] [SecondCountableTopology X]
    [LocallyCompactSpace X] [T2Space X]

instance metrizable_of_lcsc : MetrizableSpace X := inferInstance

end MetrizableLCSC
end
