/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredFullFaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredClosedFibers.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredRibbon.Part9


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open StatMech.FrontierA

noncomputable section

def fkIsingSquareWedgeFaceKey (n : Nat)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) : Int × Int :=
  let u := fkIsingSquareDartEndpoint n d
  match fkIsingSquareDartDirection n d,
      (fkIsingSquareSideCorner d.2).2 with
  | .east, .counterclockwise => (u.1 0, u.1 1)
  | .east, .clockwise => (u.1 0, u.1 1 - 1)
  | .north, .counterclockwise => (u.1 0 - 1, u.1 1)
  | .north, .clockwise => (u.1 0, u.1 1)
  | .west, .counterclockwise => (u.1 0 - 1, u.1 1 - 1)
  | .west, .clockwise => (u.1 0 - 1, u.1 1)
  | .south, .counterclockwise => (u.1 0, u.1 1 - 1)
  | .south, .clockwise => (u.1 0 - 1, u.1 1 - 1)

def fkIsingSquareInteriorFaceKey (n : Nat) (p : Int × Int) : Prop :=
  -(n : Int) ≤ p.1 ∧ p.1 < (n : Int) ∧
    -(n : Int) ≤ p.2 ∧ p.2 < (n : Int)

end
end StatMech.Universality
