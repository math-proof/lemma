module
public import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingNormalizedPartitionLimit.Part2
public import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingLieTrotter
public import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingFieldGauge.Part2
public import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingQuantumFreeEnergy
public import Theorem.StatisticalMechanics.Code.FrontierC.IsingTransfer.Part5
open Filter Matrix
open scoped Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingFreeEnergy.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

noncomputable def quantumIsingFiniteFreeEnergy
    (beta h : Real) (L : Nat) : Real :=
  -Real.log ‖quantumIsingQuantumPartition beta h L‖ / beta / L


end StatMech.FrontierA
