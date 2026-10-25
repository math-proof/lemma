/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialIncidence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBond.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredFullFaces.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialIncidence.Part4


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open StatMech.FrontierA

noncomputable section

theorem fkIsingSquareInteriorRadial_coordinates_adjacent
    (n : Nat) (hn : 0 < n)
    (e : FKIsingSquareInteriorRadialIncidence n hn) :
    let u := fkIsingSquareInteriorRadialPrimalCoordinate n hn e
    let p := fkIsingSquareInteriorRadialFaceCoordinate n hn e
    p = (u.1 + 1, u.2) ∨ p = (u.1, u.2 + 1) ∨
      p = (u.1 - 1, u.2) ∨ p = (u.1, u.2 - 1) := by
  induction e using Quot.ind with
  | _ d =>
      cases hdir : fkIsingSquareDartDirection n d.1 <;>
        cases hturn : (fkIsingSquareSideCorner d.1.2).2 <;>
        simp [fkIsingSquareInteriorRadialPrimalCoordinate,
          fkIsingSquareInteriorRadialFaceCoordinate,
          fkIsingSquareWedgeFaceKey, hdir, hturn] <;> omega


end
end StatMech.Universality
