/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/RectangularPrismTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.CylinderPathExpansion
import Theorem.StatisticalMechanics.Code.Ising.CenterMarkedPath.Part2
import Theorem.StatisticalMechanics.Code.Ising.PositiveTransferCenterObservable
import Theorem.StatisticalMechanics.Code.FrontierA.IsingRectangularDobrushinSpinFlip.Part3
import Def.StatisticalMechanics.Code.Ising.RectangularPrismTransfer.Part4
open Finset Matrix Filter Topology
open scoped BigOperators


namespace StatMech.Ising

noncomputable section

theorem rectangularPrismTransfer_isHermitian
    (J beta : Real) (m n : Nat) :
    (rectangularPrismTransfer J beta m n).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro s t
  simp only [rectangularPrismTransfer, star_trivial]
  unfold rectangularLayerVerticalInteraction
  congr 1
  rw [show (∑ p : Fin m × Fin n, spin s p * spin t p) =
      ∑ p : Fin m × Fin n, spin t p * spin s p by
    apply Finset.sum_congr rfl
    intro p hp
    ring]
  ring

theorem rectangularPrismTransfer_pos
    (J beta : Real) (m n : Nat)
    (s t : RectangularLayerConfig m n) :
    0 < rectangularPrismTransfer J beta m n s t := Real.exp_pos _

theorem rectangularPrismTransferBoundaryVector_pos
    (J beta : Real) (m n : Nat) (s : RectangularLayerConfig m n) :
    0 < rectangularPrismTransferBoundaryVector J beta m n s := Real.exp_pos _

theorem rectangularPrismTransferPathWeight_eq_exp
    (J beta : Real) (m n h : Nat)
    (q : Fin (2 * h + 1) -> RectangularLayerConfig m n) :
    rectangularPrismTransferBoundaryVector J beta m n (q 0) *
        (∏ z : Fin (2 * h),
          rectangularPrismTransfer J beta m n
            (q z.castSucc) (q z.succ)) *
        rectangularPrismTransferBoundaryVector J beta m n
          (q (Fin.last (2 * h))) =
      Real.exp
        (rectangularLayerFaceBoundary J beta (q 0) +
          rectangularLayerFaceBoundary J beta (q (Fin.last (2 * h))) +
          (∑ z : Fin (2 * h + 1),
            rectangularLayerBoltzmannInteraction J beta (q z)) +
          ∑ z : Fin (2 * h),
            rectangularLayerVerticalInteraction J beta
              (q z.castSucc) (q z.succ)) := by
  simp only [rectangularPrismTransferBoundaryVector,
    rectangularPrismTransfer]
  rw [← Real.exp_sum, ← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← Finset.sum_div, ← Finset.sum_div]
  have hfirst := Fin.sum_univ_succ
    (f := fun z : Fin (2 * h + 1) =>
      rectangularLayerBoltzmannInteraction J beta (q z))
  have hlast := Fin.sum_univ_castSucc
    (f := fun z : Fin (2 * h + 1) =>
      rectangularLayerBoltzmannInteraction J beta (q z))
  linear_combination -(1 / 2 : Real) * hfirst - (1 / 2 : Real) * hlast

theorem rectangularPrismTransferPartition_eq_sum_path
    (J beta : Real) (m n h : Nat) :
    rectangularPrismTransferPartition J beta m n h =
      ∑ q : Fin (2 * h + 1) -> RectangularLayerConfig m n,
        Real.exp
          (rectangularLayerFaceBoundary J beta (q 0) +
            rectangularLayerFaceBoundary J beta (q (Fin.last (2 * h))) +
            (∑ z : Fin (2 * h + 1),
              rectangularLayerBoltzmannInteraction J beta (q z)) +
            ∑ z : Fin (2 * h),
              rectangularLayerVerticalInteraction J beta
                (q z.castSucc) (q z.succ)) := by
  rw [rectangularPrismTransferPartition, dot_mulVec_pow_eq_sum_path]
  apply Finset.sum_congr rfl
  intro q hq
  exact rectangularPrismTransferPathWeight_eq_exp J beta m n h q


theorem rectangularPrismPlusPartition_eq_transferPartition
    (J beta : Real) (m n h : Nat) :
    rectangularPrismPlusPartition J beta m n h =
      rectangularPrismTransferPartition J beta m n h := by
  rw [rectangularPrismTransferPartition_eq_sum_path]
  unfold rectangularPrismPlusPartition Z
  rw [show (∑ sigma : RectangularPrismConfig m n h,
      Real.exp (-beta * rectangularPrismPlusEnergy J sigma)) =
      ∑ q : Fin (2 * h + 1) -> RectangularLayerConfig m n,
        Real.exp (-beta * rectangularPrismPlusEnergy J
          ((rectangularPrismLayerEquiv m n h).symm q)) by
    exact (Equiv.sum_comp (rectangularPrismLayerEquiv m n h).symm
      (fun sigma => Real.exp
        (-beta * rectangularPrismPlusEnergy J sigma))).symm]
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  exact rectangularPrismPlusExponent_eq_layers J beta
    ((rectangularPrismLayerEquiv m n h).symm q)


theorem rectangularPrismPlusPartition_eq_centerDenominator
    (J beta : Real) (m n h : Nat) :
    rectangularPrismPlusPartition J beta m n h =
      ∑ s, (((rectangularPrismTransfer J beta m n) ^ h) *ᵥ
        rectangularPrismTransferBoundaryVector J beta m n) s ^ 2 := by
  rw [rectangularPrismPlusPartition_eq_transferPartition]
  unfold rectangularPrismTransferPartition
  exact hermitian_twoTail_contraction_eq_sum_sq
    (rectangularPrismTransfer J beta m n)
    (rectangularPrismTransfer_isHermitian J beta m n)
    (rectangularPrismTransferBoundaryVector J beta m n) h


end
end StatMech.Ising
