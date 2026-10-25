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
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoxPrismEnergy


namespace StatMech.FrontierA

open scoped BigOperators

open Filter Topology

open StatMech StatMech.Lattice StatMech.Ising StatMech.Percolation

noncomputable section

theorem bond_glue_plus_oddPrismTouchIndex
    (n : Nat)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n)
    (q : OddPrismTouchIndex n) :
    bond (glue (plusField 3)
        (rectangularPrismConfigEquivSctBoxDobrushin n sigma))
        (oddPrismTouchIndexBond n q) =
      oddPrismPlusInteractionTerm n sigma q := by
  cases q <;>
    simp [oddPrismTouchIndexBond, oddPrismPlusInteractionTerm, bond_mk,
      rectangularPrismSpin, spin_glue_rectangularPrismConfigEquiv,
      spin_glue_plus_xZero, spin_glue_plus_xLast, spin_glue_plus_yZero,
      spin_glue_plus_yLast, spin_glue_plus_zZero, spin_glue_plus_zLast]

theorem sum_oddPrismPlusInteractionTerm
    (n : Nat)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) :
    (∑ q, oddPrismPlusInteractionTerm n sigma q) =
      rectangularPrismInternalInteraction sigma +
        oddRectangularPrismFaceInteraction n sigma := by
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
  simp only [oddPrismPlusInteractionTerm]
  rw [hinternal]
  unfold oddRectangularPrismFaceInteraction oddRectangularPrismFaceSum
  simp only [Fin.last, Nat.mul_comm]
  ring


theorem fvEnergy_plus_eq_rectangularPrismPlusEnergy
    (n : Nat)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) :
    fvEnergy (plusField 3) n (bondFinsetTouch 3 n) 0
        (rectangularPrismConfigEquivSctBoxDobrushin n sigma) =
      rectangularPrismPlusEnergy 1 sigma := by
  unfold fvEnergy rectangularPrismPlusEnergy
  simp only [zero_mul, sub_zero, neg_one_mul]
  change -(∑ edge ∈ bondFinsetTouch 3 n,
      bond (glue (plusField 3)
        (rectangularPrismConfigEquivSctBoxDobrushin n sigma)) edge) =
    -(rectangularPrismInternalInteraction sigma +
      rectangularPrismPlusBoundaryInteraction sigma)
  congr 1
  rw [sum_bondFinsetTouch_eq_sum_oddPrismTouchIndex]
  calc
    (∑ q, bond (glue (plusField 3)
        (rectangularPrismConfigEquivSctBoxDobrushin n sigma))
        (oddPrismTouchIndexBond n q)) =
        ∑ q, oddPrismPlusInteractionTerm n sigma q := by
      apply Finset.sum_congr rfl
      intro q _
      exact bond_glue_plus_oddPrismTouchIndex n sigma q
    _ = rectangularPrismInternalInteraction sigma +
        oddRectangularPrismFaceInteraction n sigma :=
      sum_oddPrismPlusInteractionTerm n sigma
    _ = rectangularPrismInternalInteraction sigma +
        rectangularPrismPlusBoundaryInteraction sigma := by
      rw [rectangularPrismPlusBoundaryInteraction_eq_faces]


theorem rectangularPrismPlusEnergy_eq_mul_fvEnergy
    (J : Real) (n : Nat)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) :
    rectangularPrismPlusEnergy J sigma =
      J * fvEnergy (plusField 3) n (bondFinsetTouch 3 n) 0
        (rectangularPrismConfigEquivSctBoxDobrushin n sigma) := by
  rw [fvEnergy_plus_eq_rectangularPrismPlusEnergy]
  unfold rectangularPrismPlusEnergy
  ring


theorem rectangularPrismPlusPartition_eq_fvZ
    (J beta : Real) (n : Nat) :
    rectangularPrismPlusPartition J beta (2 * n + 1) (2 * n + 1) n =
      fvZ (plusField 3) n (bondFinsetTouch 3 n) (beta * J) 0 := by
  unfold rectangularPrismPlusPartition Z fvZ fvWeight
  rw [← Equiv.sum_comp (rectangularPrismConfigEquivSctBoxDobrushin n)]
  apply Finset.sum_congr rfl
  intro sigma _
  rw [rectangularPrismPlusEnergy_eq_mul_fvEnergy]
  congr 1
  ring


end
end StatMech.FrontierA
