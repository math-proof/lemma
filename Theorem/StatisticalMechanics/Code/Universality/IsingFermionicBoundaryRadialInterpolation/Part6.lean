/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialInterpolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBoundaryRadialEnergy.Part4
import Def.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialInterpolation.Part6


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareBoundaryRadialPatchInterpolant_continuous
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (mesh : Real) :
    Continuous (fkIsingSquareBoundaryRadialPatchInterpolant n m hn hm mesh) :=
  finiteRadialGridInterpolant_continuous _ _ _


@[simp] theorem fkIsingSquareBoundaryRadialPatchInterpolant_position
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (mesh : Real) (hmesh : mesh ≠ 0) (i j : Fin m) :
    fkIsingSquareBoundaryRadialPatchInterpolant n m hn hm mesh
        (isingRadialGridPosition mesh i.1 j.1) =
      fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm i j /
        (Real.sqrt (2 * mesh) : Complex) :=
  finiteRadialGridInterpolant_position m mesh hmesh _ i j


theorem fkIsingSquareBoundaryRadialPatchInterpolant_projection
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (mesh : Real) (hmesh : 0 < mesh) (i j : Fin m)
    (s : FKIsingMedialSide) :
    isingProj (fkIsingSquareWiredDirectedTangent n hn
        (.dart (fkIsingSquareRadialPatchEdge n m hm i j, s)))
      (fkIsingSquareBoundaryRadialPatchInterpolant n m hn hm mesh
        (isingRadialGridPosition mesh i.1 j.1)) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (fkIsingSquareRadialPatchEdge n m hm i j, s)) /
        (Real.sqrt (2 * mesh) : Complex) := by
  rw [fkIsingSquareBoundaryRadialPatchInterpolant_position _ _ _ _ _ hmesh.ne']
  have hproj_div (u z : Complex) (r : Real) :
      isingProj u (z / (r : Complex)) = isingProj u z / (r : Complex) := by
    unfold isingProj
    simp
    ring
  rw [hproj_div]
  rw [fkIsingSquareBoundaryRadialPatchFullObservable_projection]


end
end StatMech.Universality
