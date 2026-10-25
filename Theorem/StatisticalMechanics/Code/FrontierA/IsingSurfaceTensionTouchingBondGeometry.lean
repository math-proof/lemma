/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionTouchingBondGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionPrismFaces.Part2
import Theorem.StatisticalMechanics.Code.IsingFK.HisingBoxClose.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionTouchingBondGeometry


namespace StatMech.FrontierA

open StatMech StatMech.Lattice StatMech.Ising StatMech.IsingFK
  StatMech.Percolation


theorem sum_oddPrismTouchIndex (n : Nat)
    (f : OddPrismTouchIndex n -> Real) :
    (∑ q, f q) =
      (∑ x, ∑ y, ∑ z, f (.xInternal x y z)) +
      (∑ x, ∑ y, ∑ z, f (.yInternal x y z)) +
      (∑ x, ∑ y, ∑ z, f (.zInternal x y z)) +
      (∑ y, ∑ z, f (.xZero y z)) +
      (∑ y, ∑ z, f (.xLast y z)) +
      (∑ x, ∑ z, f (.yZero x z)) +
      (∑ x, ∑ z, f (.yLast x z)) +
      (∑ x, ∑ y, f (.zZero x y)) +
      (∑ x, ∑ y, f (.zLast x y)) := by
  rw [Fintype.sum_equiv (oddPrismTouchIndexEquivSum n) f
    (fun q => f ((oddPrismTouchIndexEquivSum n).symm q)) (fun q => by simp)]
  simp only [Fintype.sum_sum_type]
  simp_rw [Fintype.sum_prod_type]
  simp [oddPrismTouchIndexEquivSum]
  ring


end StatMech.FrontierA
