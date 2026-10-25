/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionTouchingBondGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionPrismFaces.Part2
import Theorem.StatisticalMechanics.Code.IsingFK.HisingBoxClose.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionTouchingBondGeometry.Part2


namespace StatMech.FrontierA

open StatMech StatMech.Lattice StatMech.Ising StatMech.IsingFK
  StatMech.Percolation


def touchingBondCoordSum (i : Fin 3) : Sym2 (Site 3) -> Int :=
  Sym2.lift ⟨fun x y => x i + y i, by
    intro x y
    exact add_comm _ _⟩


def touchingBondCoordDiff (i : Fin 3) : Sym2 (Site 3) -> Nat :=
  Sym2.lift ⟨fun x y => (x i - y i).natAbs, by
    intro x y
    change (x i - y i).natAbs = (y i - x i).natAbs
    rw [show x i - y i = -(y i - x i) by ring, Int.natAbs_neg]⟩


def touchingBondKey (e : Sym2 (Site 3)) :
    (Int × Int × Int) × (Nat × Nat × Nat) :=
  ((touchingBondCoordSum 0 e, touchingBondCoordSum 1 e,
      touchingBondCoordSum 2 e),
    (touchingBondCoordDiff 0 e, touchingBondCoordDiff 1 e,
      touchingBondCoordDiff 2 e))

end StatMech.FrontierA
