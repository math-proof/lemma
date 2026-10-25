/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBoundaryRadialEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.Part26
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWindowRealization.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBoundaryRadialEnergy


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareRadialPatchEdge_not_mem_perimeter
    (n m : Nat) (hm : m ≤ n) (i j : Fin m) :
    (fkIsingSquareRadialPatchEdge n m hm i j).1 ∉
      fkIsingSquarePerimeterPrimalEdgeFinset n := by
  exact fkIsingSquareInteriorRadialCell_not_mem_perimeter n
    (fkIsingSquareRadialPatchCell n m hm i j)


theorem fkIsingSquareBoundaryRadialPatchFullObservable_projection
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (i j : Fin m) (s : FKIsingMedialSide) :
    isingProj
        (fkIsingSquareWiredDirectedTangent n hn
          (.dart (fkIsingSquareRadialPatchEdge n m hm i j, s)))
        (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm i j) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareRadialPatchEdge n m hm i j, s)) := by
  exact fkIsingSquareBoundaryFullMedialObservable_projection n hn _
    (fkIsingSquareRadialPatchEdge_not_mem_perimeter n m hm i j) s


end
end StatMech.Universality
