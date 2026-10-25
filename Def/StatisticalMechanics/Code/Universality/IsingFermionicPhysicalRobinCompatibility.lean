/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRobinCompatibility.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicProjectedFullMedialInterpolation.Part5
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareCaratheodory.Part5
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryLayerConsistency.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCalibratedRobinConsistency


namespace StatMech.Universality

open Filter Metric Set Topology

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingExpandingBoundarySquareRadialDart
    (k m : Nat) (hm : m ≤ fkIsingExpandingSquareSide k)
    (i j : Fin m) (s : FKIsingMedialSide) :
    fkIsingExpandingBoundarySquareCaratheodoryApproximation.M k :=
  .dart (fkIsingSquareRadialPatchEdge
    (fkIsingExpandingSquareSide k) m hm i j, s)


def fkIsingExpandingBoundarySquareRadialSamplePosition
    (k : Nat) (i j : Nat) : Complex :=
  isingRadialGridPosition (fkIsingExpandingSquareScale k) i j


noncomputable def fkIsingExpandingBoundarySquareRadialTwoScaleInterpolant
    (k m : Nat) (hm : m ≤ fkIsingExpandingSquareSide k) :
    Complex → Complex :=
  fkIsingSquareBoundaryRadialPatchTwoScaleInterpolant
    (fkIsingExpandingSquareSide k) m
    (fkIsingExpandingSquareSide_pos k) hm
    (fkIsingExpandingSquareScale k)
    (fkIsingExpandingBoundarySquareCaratheodoryApproximation.mesh k)

end
end StatMech.Universality
