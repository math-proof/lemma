/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerLaplacian
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part9
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialInterpolation.Part7
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareCenteredRadialPatchVertex
    (n : Nat) (i j : Fin (2 * n)) : (fkSquareBoxPlanar n).V := by
  let q := centeredRadialHalf i.1 j.1
  refine ⟨![(q : Int) - (n : Int), (i.1 : Int) - (q : Int)], ?_⟩
  intro k
  fin_cases k
  · change ((q : Int) - (n : Int)).natAbs <= n
    apply natAbs_le_of_int_bounds
    · dsimp only [q, centeredRadialHalf]
      have hi := i.2
      have hj := j.2
      omega
    · dsimp only [q, centeredRadialHalf]
      have hi := i.2
      have hj := j.2
      omega
  · change ((i.1 : Int) - (q : Int)).natAbs <= n
    apply natAbs_le_of_int_bounds
    · dsimp only [q, centeredRadialHalf]
      have hi := i.2
      have hj := j.2
      omega
    · dsimp only [q, centeredRadialHalf]
      have hi := i.2
      have hj := j.2
      omega


def fkIsingSquareCenteredRadialPatchDirection (i j : Nat) :
    FKIsingSquareDirection :=
  if Even (i + j) then .east else .north

end
end StatMech.Universality
