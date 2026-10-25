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
import Def.StatisticalMechanics.Code.Ising.RectangularPrismTransfer.Part5
open Finset Matrix Filter Topology
open scoped BigOperators


namespace StatMech.Ising

noncomputable section

theorem rectangularPrismPlusCentralSpinNumerator_eq_markedPath
    (J beta : Real) (m n h : Nat) (p : Fin m × Fin n) :
    rectangularPrismPlusCentralSpinNumerator J beta m n h p =
      centerMarkedPathSum
        (rectangularPrismTransfer J beta m n)
        (rectangularPrismTransferBoundaryVector J beta m n)
        (fun s => spin s p) h := by
  unfold rectangularPrismPlusCentralSpinNumerator centerMarkedPathSum
  rw [show (∑ sigma : RectangularPrismConfig m n h,
      rectangularPrismSpin sigma p.1 p.2 ⟨h, by omega⟩ *
        Real.exp (-beta * rectangularPrismPlusEnergy J sigma)) =
      ∑ q : Fin (2 * h + 1) -> RectangularLayerConfig m n,
        rectangularPrismSpin ((rectangularPrismLayerEquiv m n h).symm q)
            p.1 p.2 ⟨h, by omega⟩ *
          Real.exp (-beta * rectangularPrismPlusEnergy J
            ((rectangularPrismLayerEquiv m n h).symm q)) by
    exact (Equiv.sum_comp (rectangularPrismLayerEquiv m n h).symm
      (fun sigma =>
        rectangularPrismSpin sigma p.1 p.2 ⟨h, by omega⟩ *
          Real.exp (-beta * rectangularPrismPlusEnergy J sigma))).symm]
  apply Finset.sum_congr rfl
  intro q hq
  change spin (q ⟨h, by omega⟩) p *
      Real.exp (-beta * rectangularPrismPlusEnergy J
        ((rectangularPrismLayerEquiv m n h).symm q)) =
    rectangularPrismTransferBoundaryVector J beta m n (q 0) *
      spin (q ⟨h, by omega⟩) p *
      (∏ z : Fin (2 * h), rectangularPrismTransfer J beta m n
        (q z.castSucc) (q z.succ)) *
      rectangularPrismTransferBoundaryVector J beta m n
        (q (Fin.last (2 * h)))
  rw [rectangularPrismPlusExponent_eq_layers]
  simp only [rectangularPrismLayer_equiv_symm]
  rw [← rectangularPrismTransferPathWeight_eq_exp J beta m n h q]
  ring

theorem rectangularPrismPlusCentralSpinNumerator_eq_transferSquare
    (J beta : Real) (m n h : Nat) (p : Fin m × Fin n) :
    rectangularPrismPlusCentralSpinNumerator J beta m n h p =
      ∑ s, spin s p *
        (((rectangularPrismTransfer J beta m n) ^ h) *ᵥ
          rectangularPrismTransferBoundaryVector J beta m n) s ^ 2 := by
  rw [rectangularPrismPlusCentralSpinNumerator_eq_markedPath]
  apply centerMarkedPathSum_eq_sum_sq
  intro s t
  simpa using
    (rectangularPrismTransfer_isHermitian J beta m n).apply t s


end
end StatMech.Ising
