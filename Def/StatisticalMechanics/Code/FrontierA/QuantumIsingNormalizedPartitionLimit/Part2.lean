/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingNormalizedPartitionLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingUniformMode.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingSectorProductComparison
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingNormalizedPartitionSandwich
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingSpatialSeam.Part8
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingNormalizedPartitionLimit
open Filter
open scoped Topology


namespace StatMech.FrontierA

noncomputable def quantumIsingCofinalPeriodicTrotterFreeEnergy
    (beta h : Real) (n : Nat) : Real :=
  quantumIsingPeriodicTrotterAction beta h (n + 3) (n + 3) /
    (n + 3 : Real)

end StatMech.FrontierA
