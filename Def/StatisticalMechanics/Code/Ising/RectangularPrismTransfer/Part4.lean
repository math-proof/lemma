module
public import Theorem.StatisticalMechanics.Code.Ising.CylinderPathExpansion
public import Theorem.StatisticalMechanics.Code.Ising.CenterMarkedPath.Part2
public import Theorem.StatisticalMechanics.Code.Ising.PositiveTransferCenterObservable
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingRectangularDobrushinSpinFlip.Part3
public import Theorem.StatisticalMechanics.Code.Ising.RectangularPrismTransfer.Part3
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

def rectangularPrismTransfer (J beta : Real) (m n : Nat) :
    Matrix (RectangularLayerConfig m n) (RectangularLayerConfig m n) Real :=
  fun s t => Real.exp
    (rectangularLayerBoltzmannInteraction J beta s / 2 +
      rectangularLayerVerticalInteraction J beta s t +
      rectangularLayerBoltzmannInteraction J beta t / 2)


def rectangularPrismTransferBoundaryVector (J beta : Real) (m n : Nat) :
    RectangularLayerConfig m n -> Real :=
  fun s => Real.exp
    (rectangularLayerBoltzmannInteraction J beta s / 2 +
      rectangularLayerFaceBoundary J beta s)


def rectangularPrismTransferPartition
    (J beta : Real) (m n h : Nat) : Real :=
  let A := rectangularPrismTransfer J beta m n
  let a := rectangularPrismTransferBoundaryVector J beta m n
  ∑ s, a s * ((A ^ (2 * h)) *ᵥ a) s

end
end StatMech.Ising
