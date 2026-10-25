/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/POUSeqDensityHelpers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.PartitionOfUnity
set_option linter.unusedSectionVars false

open TopologicalSpace Metric Set Filter Topology


noncomputable section

section MetrizableLCSC

variable (X : Type*) [TopologicalSpace X] [SecondCountableTopology X]
    [LocallyCompactSpace X] [T2Space X]

instance metrizable_of_lcsc : MetrizableSpace X := inferInstance

end MetrizableLCSC
end
