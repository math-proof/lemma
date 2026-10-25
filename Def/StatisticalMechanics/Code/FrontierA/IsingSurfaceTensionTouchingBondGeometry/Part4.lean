/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionTouchingBondGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionPrismFaces.Part2
import Theorem.StatisticalMechanics.Code.IsingFK.HisingBoxClose.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionTouchingBondGeometry.Part3


namespace StatMech.FrontierA

open StatMech StatMech.Lattice StatMech.Ising StatMech.IsingFK
  StatMech.Percolation


noncomputable def oddPrismTouchIndexEquivBondFinset (n : Nat) :
    OddPrismTouchIndex n ≃ {e // e ∈ bondFinsetTouch 3 n} :=
  Equiv.ofBijective
    (fun q => ⟨oddPrismTouchIndexBond n q,
      oddPrismTouchIndexBond_mem n q⟩)
    ⟨fun q r h => oddPrismTouchIndexBond_injective n
        (congrArg Subtype.val h),
      oddPrismTouchIndexBond_surjective n⟩


end StatMech.FrontierA
