/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredOneVisitInsertedPhase
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredTangentCode
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part12


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

theorem fkIsingSquareWiredExpanded_bulge_steps
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    (fkIsingSquareWiredExpandedIntPosition n hn (.inr k) =
      fkIsingSquareWiredExpandedIntPosition n hn
          (fkIsingSquareWiredExpandedStart n hn k) +
        fkIsingSquareWiredUnitDiagonalStep 1) ∧
    (fkIsingSquareWiredExpandedIntPosition n hn
        (fkIsingSquareWiredExpandedMiddle n hn k) =
      fkIsingSquareWiredExpandedIntPosition n hn (.inr k) +
        fkIsingSquareWiredUnitDiagonalStep 3) ∧
    (fkIsingSquareWiredExpandedIntPosition n hn
        (fkIsingSquareWiredExpandedEnd n hn k) =
      fkIsingSquareWiredExpandedIntPosition n hn
          (fkIsingSquareWiredExpandedMiddle n hn k) +
        fkIsingSquareWiredUnitDiagonalStep 2) := by
  simp [fkIsingSquareWiredExpandedIntPosition,
    fkIsingSquareWiredExpandedStart,
    fkIsingSquareWiredExpandedMiddle,
    fkIsingSquareWiredExpandedEnd,
    fkIsingSquareWiredSlotIntPosition,
    fkIsingSquareWiredPortOctagonOffset,
    fkIsingSquareWiredUnitDiagonalStep,
    fkIsingSquareLeftVerticalLower, fkIsingSquareLeftVerticalUpper,
    Prod.ext_iff]
  omega


end
end StatMech.Universality
