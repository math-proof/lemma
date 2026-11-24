module
public import Theorem.StatisticalMechanics.Code.Ising.CylinderPathExpansion
public import Theorem.StatisticalMechanics.Code.Ising.CenterMarkedPath.Part2
public import Theorem.StatisticalMechanics.Code.Ising.PositiveTransferCenterObservable
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingRectangularDobrushinSpinFlip.Part3
public import Theorem.StatisticalMechanics.Code.Ising.RectangularPrismTransfer.Part5
open Finset Matrix Filter Topology
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/RectangularPrismTransfer.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Ising

noncomputable section

def rectangularPrismPlusCentralSpinMean
    (J beta : Real) (m n : Nat) (p : Fin m × Fin n) (h : Nat) : Real :=
  rectangularPrismPlusCentralSpinNumerator J beta m n h p /
    rectangularPrismPlusPartition J beta m n h


end
end StatMech.Ising
