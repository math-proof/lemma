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
import Def.StatisticalMechanics.Code.Ising.RectangularPrismTransfer.Part7
open Finset Matrix Filter Topology
open scoped BigOperators


namespace StatMech.Ising

noncomputable section

theorem rectangularPrismPlusCentralSpinMean_eq_transfer
    (J beta : Real) (m n : Nat) (p : Fin m × Fin n) (h : Nat) :
    rectangularPrismPlusCentralSpinMean J beta m n p h =
      rectangularPrismCenterSpinMean J beta m n p h := by
  unfold rectangularPrismPlusCentralSpinMean rectangularPrismCenterSpinMean
  rw [rectangularPrismPlusCentralSpinNumerator_eq_transferSquare,
    rectangularPrismPlusPartition_eq_centerDenominator]


theorem rectangularPrismCenterSpinMean_tendsto
    (J beta : Real) (m n : Nat) (p : Fin m × Fin n) :
    ∃ m0 : Real, Tendsto
      (rectangularPrismCenterSpinMean J beta m n p)
      atTop (nhds m0) := by
  obtain ⟨lam, hlam, u, hupos, hunorm, hueig, hlim⟩ :=
    positiveTransfer_centerObservable_tendsto
      (rectangularPrismTransfer J beta m n)
      (rectangularPrismTransfer_isHermitian J beta m n)
      (rectangularPrismTransfer_pos J beta m n)
      (rectangularPrismTransferBoundaryVector J beta m n)
      (rectangularPrismTransferBoundaryVector_pos J beta m n)
      (fun s => spin s p)
  exact ⟨(∑ s, spin s p * (u s) ^ 2) / ∑ s, (u s) ^ 2, by
    simpa [rectangularPrismCenterSpinMean] using hlim⟩

theorem rectangularPrismPlusCentralSpinMean_tendsto
    (J beta : Real) (m n : Nat) (p : Fin m × Fin n) :
    ∃ m0 : Real, Tendsto
      (rectangularPrismPlusCentralSpinMean J beta m n p)
      atTop (nhds m0) := by
  obtain ⟨m0, hlim⟩ := rectangularPrismCenterSpinMean_tendsto J beta m n p
  refine ⟨m0, ?_⟩
  rw [show rectangularPrismPlusCentralSpinMean J beta m n p =
      rectangularPrismCenterSpinMean J beta m n p by
    funext h
    exact rectangularPrismPlusCentralSpinMean_eq_transfer J beta m n p h]
  exact hlim

end
end StatMech.Ising
