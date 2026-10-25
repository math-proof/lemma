/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionTouchingBondGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionPrismFaces.Part2
import Theorem.StatisticalMechanics.Code.IsingFK.HisingBoxClose.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionTouchingBondGeometry.Part4


namespace StatMech.FrontierA

open StatMech StatMech.Lattice StatMech.Ising StatMech.IsingFK
  StatMech.Percolation


theorem sum_bondFinsetTouch_eq_sum_oddPrismTouchIndex
    (n : Nat) (f : Sym2 (Site 3) -> Real) :
    (∑ edge ∈ bondFinsetTouch 3 n, f edge) =
      ∑ q : OddPrismTouchIndex n, f (oddPrismTouchIndexBond n q) := by
  have hattach := Finset.sum_attach (bondFinsetTouch 3 n) f
  have hsubtype :
      (∑ edge : {e // e ∈ bondFinsetTouch 3 n}, f edge.1) =
        ∑ edge ∈ bondFinsetTouch 3 n, f edge := by
    simpa using hattach
  rw [← hsubtype]
  exact (Equiv.sum_comp (oddPrismTouchIndexEquivBondFinset n)
    (fun edge => f edge.1)).symm

end StatMech.FrontierA
