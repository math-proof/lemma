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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part14


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

theorem fkIsingSquareWiredSlotRingBulge_midpoint_ne
    (n : Nat) (hn : 0 < n)
    (u : (fkSquareBoxPlanar n).V) (i : Fin 8)
    (hkeep : ¬fkIsingSquareWiredLeftRingRemoved n (u, i))
    (k : Fin (2 * n)) (j : Fin 3) :
    fkIsingSquareWiredSlotIntPosition n (u, i) +
          fkIsingSquareWiredSlotIntPosition n (u, i + 1) ≠
        fkIsingSquareWiredExpandedBulgeMidpoint n hn k j := by
  intro hmid
  have hx := congrArg Prod.fst hmid
  have hy := congrArg Prod.snd hmid
  have bu0 := fkIsingSquareVertex_coordinate_bounds n u 0
  have bu1 := fkIsingSquareVertex_coordinate_bounds n u 1
  fin_cases i <;> fin_cases j <;>
    simp [fkIsingSquareWiredSlotIntPosition,
      fkIsingSquareWiredPortOctagonOffset,
      fkIsingSquareWiredExpandedBulgeMidpoint,
      fkIsingSquareWiredExpandedBulgeEndpoints,
      fkIsingSquareWiredExpandedIntPosition,
      fkIsingSquareWiredExpandedStart,
      fkIsingSquareWiredExpandedMiddle,
      fkIsingSquareWiredExpandedEnd,
      fkIsingSquareLeftVerticalLower,
      fkIsingSquareLeftVerticalUpper,
      fkIsingSquareWiredLeftRingRemoved] at hx hy hkeep <;>
    omega


end
end StatMech.Universality
