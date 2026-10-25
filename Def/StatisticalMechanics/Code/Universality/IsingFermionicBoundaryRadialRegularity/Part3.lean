/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBoundaryAverage
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointPointwise
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialRegularity.Part3


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

noncomputable def fkIsingSquareBoundaryRadialPatchDeepVariation
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (r : Nat) : Real :=
  (∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm (by omega) r,
      |FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue
            n m hn hm d.snd -
        FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue
            n m hn hm d.fst|) +
    ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r,
      |FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue
            n m hn hm hm2 d.snd -
        FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue
            n m hn hm hm2 d.fst|

end
end StatMech.Universality
