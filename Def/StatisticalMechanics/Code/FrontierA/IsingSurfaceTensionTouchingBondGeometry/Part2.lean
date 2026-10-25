/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionTouchingBondGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionPrismFaces.Part2
import Theorem.StatisticalMechanics.Code.IsingFK.HisingBoxClose.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionTouchingBondGeometry


namespace StatMech.FrontierA

open StatMech StatMech.Lattice StatMech.Ising StatMech.IsingFK
  StatMech.Percolation


def oddPrismTouchIndexBond (n : Nat) :
    OddPrismTouchIndex n -> Sym2 (Site 3) := by
  let e := rectangularPrismSiteEquivSctBoxDobrushin n
  intro q
  exact match q with
  | .xInternal x y z =>
      s((e ⟨⟨x.val, by omega⟩, y, z⟩).1,
        (e ⟨⟨x.val + 1, by omega⟩, y, z⟩).1)
  | .yInternal x y z =>
      s((e ⟨x, ⟨y.val, by omega⟩, z⟩).1,
        (e ⟨x, ⟨y.val + 1, by omega⟩, z⟩).1)
  | .zInternal x y z =>
      s((e ⟨x, y, ⟨z.val, by omega⟩⟩).1,
        (e ⟨x, y, ⟨z.val + 1, by omega⟩⟩).1)
  | .xZero y z =>
      let u := (e ⟨0, y, z⟩).1
      s(u, coordShift u 0 (-1))
  | .xLast y z =>
      let u := (e ⟨Fin.last (2 * n), y, z⟩).1
      s(u, coordShift u 0 1)
  | .yZero x z =>
      let u := (e ⟨x, 0, z⟩).1
      s(u, coordShift u 1 (-1))
  | .yLast x z =>
      let u := (e ⟨x, Fin.last (2 * n), z⟩).1
      s(u, coordShift u 1 1)
  | .zZero x y =>
      let u := (e ⟨x, y, 0⟩).1
      s(u, coordShift u 2 1)
  | .zLast x y =>
      let u := (e ⟨x, y, Fin.last (2 * n)⟩).1
      s(u, coordShift u 2 (-1))


end StatMech.FrontierA
