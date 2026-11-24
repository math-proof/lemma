module
public import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingFreeEnergy
public import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingZeroField
open Filter Matrix
open scoped Topology BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingZeroField.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

def quantumIsingConfigTransferEquiv (L : Nat) :
    QuantumIsingChainConfig L ≃ (Fin L → Fin 2) :=
  Equiv.piCongrRight fun _ ↦ quantumIsingBoolTransferEquiv

end StatMech.FrontierA
