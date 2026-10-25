/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionTouchingBondGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionPrismFaces.Part2
import Theorem.StatisticalMechanics.Code.IsingFK.HisingBoxClose.Part3
import Abbrev.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionTouchingBondGeometry


namespace StatMech.FrontierA

open StatMech StatMech.Lattice StatMech.Ising StatMech.IsingFK
  StatMech.Percolation


def oddPrismTouchIndexEquivSum (n : Nat) :
    OddPrismTouchIndex n ≃ OddPrismTouchIndexSum n where
  toFun
    | .xInternal x y z => .inl (x, y, z)
    | .yInternal x y z => .inr (.inl (x, y, z))
    | .zInternal x y z => .inr (.inr (.inl (x, y, z)))
    | .xZero y z => .inr (.inr (.inr (.inl (y, z))))
    | .xLast y z => .inr (.inr (.inr (.inr (.inl (y, z)))))
    | .yZero x z => .inr (.inr (.inr (.inr (.inr (.inl (x, z))))))
    | .yLast x z => .inr (.inr (.inr (.inr (.inr (.inr (.inl (x, z)))))))
    | .zZero x y =>
        .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (x, y))))))))
    | .zLast x y =>
        .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (x, y))))))))
  invFun
    | .inl (x, y, z) => .xInternal x y z
    | .inr (.inl (x, y, z)) => .yInternal x y z
    | .inr (.inr (.inl (x, y, z))) => .zInternal x y z
    | .inr (.inr (.inr (.inl (y, z)))) => .xZero y z
    | .inr (.inr (.inr (.inr (.inl (y, z))))) => .xLast y z
    | .inr (.inr (.inr (.inr (.inr (.inl (x, z)))))) => .yZero x z
    | .inr (.inr (.inr (.inr (.inr (.inr (.inl (x, z))))))) => .yLast x z
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (x, y)))))))) =>
        .zZero x y
    | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (x, y)))))))) =>
        .zLast x y
  left_inv q := by cases q <;> rfl
  right_inv q := by
    rcases q with q | q
    · rcases q with ⟨x, y, z⟩; rfl
    · rcases q with q | q
      · rcases q with ⟨x, y, z⟩; rfl
      · rcases q with q | q
        · rcases q with ⟨x, y, z⟩; rfl
        · rcases q with q | q
          · rcases q with ⟨x, y⟩; rfl
          · rcases q with q | q
            · rcases q with ⟨x, y⟩; rfl
            · rcases q with q | q
              · rcases q with ⟨x, y⟩; rfl
              · rcases q with q | q
                · rcases q with ⟨x, y⟩; rfl
                · rcases q with q | q <;> rcases q with ⟨x, y⟩ <;> rfl


end StatMech.FrontierA
