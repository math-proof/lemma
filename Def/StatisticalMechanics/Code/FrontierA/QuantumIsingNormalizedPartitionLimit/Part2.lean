module
public import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingUniformMode.Part5
public import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingSectorProductComparison
public import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingNormalizedPartitionSandwich
public import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingSpatialSeam.Part8
public import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingNormalizedPartitionLimit
open Filter
open scoped Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingNormalizedPartitionLimit.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

noncomputable def quantumIsingCofinalPeriodicTrotterFreeEnergy
    (beta h : Real) (n : Nat) : Real :=
  quantumIsingPeriodicTrotterAction beta h (n + 3) (n + 3) /
    (n + 3 : Real)

end StatMech.FrontierA
