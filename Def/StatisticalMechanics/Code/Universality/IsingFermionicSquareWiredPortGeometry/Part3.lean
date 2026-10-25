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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part2


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

noncomputable def fkIsingSquareWiredUnitDiagonalSimplePolygon
    {m : Nat} [NeZero m] (vertex : Fin m → Int × Int)
    (direction : Fin m → Fin 4)
    (hstep : ∀ i, vertex (i + 1) =
      vertex i + fkIsingSquareWiredUnitDiagonalStep (direction i))
    (hm : 3 ≤ m) (hinjective : Function.Injective vertex)
    (hmidpoint : Function.Injective
      (fun i => vertex i + vertex (i + 1))) :
    StatMech.FrontierA.KWFiniteSimplePolygon m where
  vertex := fun i => fkIsingSquareWiredIntPoint (vertex i)
  three_le := hm
  vertex_injective := fkIsingSquareWiredIntPoint_injective.comp hinjective
  vertex_not_strictly_between := by
    intro i j _ _
    rw [hstep i]
    exact fkIsingSquareWiredIntPoint_not_strictly_between_unitDiagonal
      (vertex i) (vertex j) (direction i)
  edgeInteriors_disjoint := by
    intro i j hij
    apply Set.disjoint_left.2
    intro z hzi hzj
    apply hij
    apply hmidpoint
    change vertex i + vertex (i + 1) = vertex j + vertex (j + 1)
    rw [hstep i, hstep j]
    exact fkIsingSquareWiredUnitDiagonal_open_intersection_midpoint_eq
      (vertex i) (vertex j) (direction i) (direction j) z
      (by simpa [hstep i] using hzi) (by simpa [hstep j] using hzj)


end
end StatMech.Universality
