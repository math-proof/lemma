/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialRectangle.Part6
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDirichletLimit.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialPatch.Part3


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open Filter Set Topology

noncomputable section

def fkIsingSquareRadialPatchCell
    (n m : Nat) (hm : m ≤ n) (i j : Fin m) :
    FKIsingSquareInteriorRadialCell n := by
  refine ⟨fkIsingSquareRadialPatchEdge n m hm i j, ?_⟩
  intro s
  have hi : i.1 < n := lt_of_lt_of_le i.2 hm
  have hj : j.1 < n := lt_of_lt_of_le j.2 hm
  have hq := fkIsingSquareRadialPatchHalf_lt hm i j
  by_cases heven : Even (i.1 + j.1)
  · have hmod : (i.1 + j.1) % 2 = 0 := Nat.even_iff.mp heven
    rw [fkIsingSquareRadialPatchWedgeFaceKey_of_even n m hm i j heven s]
    cases s <;> simp [fkIsingSquareInteriorFaceKey] <;> omega
  · have hmod : (i.1 + j.1) % 2 = 1 := by
      exact Nat.not_even_iff.mp heven
    rw [fkIsingSquareRadialPatchWedgeFaceKey_of_odd n m hm i j heven s]
    cases s <;> simp [fkIsingSquareInteriorFaceKey] <;> omega


def fkIsingSquareRadialPatchRightSide (i j : Nat) : FKIsingMedialSide :=
  if Even (i + j) then .north else .east


def fkIsingSquareRadialPatchLeftSide (i j : Nat) : FKIsingMedialSide :=
  if Even (i + j) then .south else .west


def fkIsingSquareRadialPatchBottomSide (i j : Nat) : FKIsingMedialSide :=
  if Even (i + j) then .west else .north


def fkIsingSquareRadialPatchTopSide (i j : Nat) : FKIsingMedialSide :=
  if Even (i + j) then .east else .south

end
end StatMech.Universality
