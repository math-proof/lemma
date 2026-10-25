/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareCaratheodory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBoundaryScaledDomain.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryApproximation.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareCaratheodory.Part2


namespace StatMech.Universality

open Filter Set Topology Metric

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section

def fkIsingExpandingSquareCarrier (k : Nat) : Set Complex :=
  {z | ∃ a : FKIsingSquareWiredCarrier (fkIsingExpandingSquareSide k),
    dist z (fkIsingSquareWiredPerturbedCarrierPosition
      (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
      (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k) a) ≤
        fkIsingExpandingSquareMesh k}

end
end StatMech.Universality
