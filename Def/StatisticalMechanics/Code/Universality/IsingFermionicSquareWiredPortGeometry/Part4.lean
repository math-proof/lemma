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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part3


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

def fkIsingSquareWiredPortIntPosition (n : Nat)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) : Int × Int :=
  let edge := fkIsingSquareOrientedEdge n d.1
  let x := edge.tail.1 0
  let y := edge.tail.1 1
  match edge.axis, d.2 with
  | .horizontal, .west => (4 * x + 1, 4 * y)
  | .horizontal, .south => (4 * x + 2, 4 * y - 1)
  | .horizontal, .east => (4 * x + 3, 4 * y)
  | .horizontal, .north => (4 * x + 2, 4 * y + 1)
  | .vertical, .west => (4 * x - 1, 4 * y + 2)
  | .vertical, .south => (4 * x, 4 * y + 1)
  | .vertical, .east => (4 * x + 1, 4 * y + 2)
  | .vertical, .north => (4 * x, 4 * y + 3)

end
end StatMech.Universality
