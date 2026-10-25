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
import Def.StatisticalMechanics.Code.Ising.RectangularPrismTransfer.Part6
open Finset Matrix Filter Topology
open scoped BigOperators


namespace StatMech.Ising

noncomputable section

theorem rectangularPrismPlusPartition_log_div_tendsto
    (J beta : Real) (m n : Nat) :
    ∃ lam : Real, 0 < lam ∧
      Tendsto (fun h : Nat =>
        Real.log (rectangularPrismPlusPartition J beta m n h) /
          (2 * h : Real)) atTop (nhds (Real.log lam)) := by
  obtain ⟨lam, hlam, hlim⟩ :=
    positiveTransfer_log_dotProduct_div_tendsto
      (rectangularPrismTransfer J beta m n)
      (rectangularPrismTransfer_isHermitian J beta m n)
      (rectangularPrismTransfer_pos J beta m n)
      (rectangularPrismTransferBoundaryVector J beta m n)
      (rectangularPrismTransferBoundaryVector J beta m n)
      (rectangularPrismTransferBoundaryVector_pos J beta m n)
      (rectangularPrismTransferBoundaryVector_pos J beta m n)
  refine ⟨lam, hlam, ?_⟩
  rw [show (fun h : Nat =>
      Real.log (rectangularPrismPlusPartition J beta m n h) /
        (2 * h : Real)) =
      fun h : Nat =>
        (Real.log (rectangularPrismTransferPartition J beta m n h) /
          (2 * h : Real)) by
    funext h
    rw [rectangularPrismPlusPartition_eq_transferPartition]]
  have htwo : Tendsto (fun h : Nat => 2 * h) atTop atTop := by
    refine tendsto_atTop.2 (fun N => ?_)
    exact eventually_atTop.2 ⟨N, fun h hh => by omega⟩
  have hcomp := hlim.comp htwo
  simpa [rectangularPrismTransferPartition, Function.comp_def] using hcomp


end
end StatMech.Ising
