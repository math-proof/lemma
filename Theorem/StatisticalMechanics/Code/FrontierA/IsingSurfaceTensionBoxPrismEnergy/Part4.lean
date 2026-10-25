/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionTouchingBondGeometry.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionFiniteVolume.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoundaryBridge.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoxPrismEnergy.Part3


namespace StatMech.FrontierA

open scoped BigOperators

open Filter Topology

open StatMech StatMech.Lattice StatMech.Ising StatMech.Percolation

noncomputable section

theorem bond_glue_interface_oddPrismTouchIndex
    (n : Nat) (hn : 0 < n)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n)
    (q : OddPrismTouchIndex n) :
    bond (glue (interfaceField (⟨2, by omega⟩ : Fin 3))
        (rectangularPrismConfigEquivSctBoxDobrushin n sigma))
        (oddPrismTouchIndexBond n q) =
      oddPrismDobrushinInteractionTerm n sigma q := by
  cases q <;>
    simp [oddPrismTouchIndexBond, oddPrismDobrushinInteractionTerm,
      oddPrismPlusInteractionTerm, bond_mk, rectangularPrismSpin,
      spin_glue_rectangularPrismConfigEquiv]
  case xZero y z =>
    rw [spin_glue_interface_of_not_mem_coord_at n _ rfl _
      (oddPrism_xZero_exterior_not_mem n y z) z (by simp [coordShift])]
    ring
  case xLast y z =>
    rw [spin_glue_interface_of_not_mem_coord_at n _ rfl _
      (oddPrism_xLast_exterior_not_mem n y z) z (by simp [coordShift])]
    ring
  case yZero x z =>
    rw [spin_glue_interface_of_not_mem_coord_at n _ rfl _
      (oddPrism_yZero_exterior_not_mem n x z) z (by simp [coordShift])]
    ring
  case yLast x z =>
    rw [spin_glue_interface_of_not_mem_coord_at n _ rfl _
      (oddPrism_yLast_exterior_not_mem n x z) z (by simp [coordShift])]
    ring
  case zZero x y =>
    rw [spin_glue_interface_zZero_at n _ rfl]
    ring
  case zLast x y =>
    rw [spin_glue_interface_zLast_at n hn _ rfl]
    ring

theorem sum_oddPrismDobrushinInteractionTerm
    (n : Nat)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) :
    (∑ q, oddPrismDobrushinInteractionTerm n sigma q) =
      rectangularPrismInternalInteraction sigma +
        oddRectangularPrismDobrushinFaceInteraction n sigma := by
  have hinternal :
      (∑ x : Fin (2 * n), ∑ y : Fin (2 * n + 1),
          ∑ z : Fin (2 * n + 1),
            rectangularPrismSpin sigma ⟨x.val, by omega⟩ y z *
              rectangularPrismSpin sigma ⟨x.val + 1, by omega⟩ y z) +
      (∑ x : Fin (2 * n + 1), ∑ y : Fin (2 * n),
          ∑ z : Fin (2 * n + 1),
            rectangularPrismSpin sigma x ⟨y.val, by omega⟩ z *
              rectangularPrismSpin sigma x ⟨y.val + 1, by omega⟩ z) +
      (∑ x : Fin (2 * n + 1), ∑ y : Fin (2 * n + 1),
          ∑ z : Fin (2 * n),
            rectangularPrismSpin sigma x y ⟨z.val, by omega⟩ *
              rectangularPrismSpin sigma x y ⟨z.val + 1, by omega⟩) =
        rectangularPrismInternalInteraction sigma := by
    unfold rectangularPrismInternalInteraction
    rfl
  rw [sum_oddPrismTouchIndex]
  simp only [oddPrismDobrushinInteractionTerm, oddPrismPlusInteractionTerm]
  rw [hinternal]
  unfold oddRectangularPrismDobrushinFaceInteraction
    oddRectangularPrismFaceSum
  simp only [Fin.last, Nat.mul_comm]
  ring


end
end StatMech.FrontierA
