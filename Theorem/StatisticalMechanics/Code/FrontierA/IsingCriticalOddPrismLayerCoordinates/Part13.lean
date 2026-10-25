/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalUnequalBridgeGeometry.Part3
import Theorem.StatisticalMechanics.Code.Ising.GHSLebowitz.Part11
import Theorem.StatisticalMechanics.Code.Ising.IsingFKGLayer
import Theorem.StatisticalMechanics.Code.Ising.RectangularPrismTransfer.Part7
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part13


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

theorem oddPrismFullTiltedWeight_eq_pathWeight
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) :
    wJ (oddPrismInternalGraph n).edgeFinset (fun _ => beta)
        (fun v => beta * oddPrismPlusField n v) sigma *
      Real.exp ((r - beta) * oddPrismFullSeamInteraction n sigma) =
        oddPrismFullTiltedPathWeight beta n r sigma := by
  let A := rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1)
  let a := rectangularPrismTransferBoundaryVector
    1 beta (2 * n + 1) (2 * n + 1)
  let q := rectangularPrismLayer sigma
  have hw : wJ (oddPrismInternalGraph n).edgeFinset (fun _ => beta)
        (fun v => beta * oddPrismPlusField n v) sigma =
      Real.exp (-beta * rectangularPrismPlusEnergy 1 sigma) := by
    rw [oddPrismInternalGraph_edgeFinset]
    calc
      wJ (oddPrismInternalEdges n) (fun _ => beta)
          (fun v => beta * oddPrismPlusField n v) sigma =
        Real.exp (beta * inhomogeneousInteraction (oddPrismInternalEdges n)
          (fun _ => 1) (oddPrismPlusField n) sigma) := by
            simpa using scaled_wJ_eq_exp_interaction (oddPrismInternalEdges n)
              (fun _ => 1) (oddPrismPlusField n) sigma beta
      _ = _ := by
        rw [oddPrism_plus_inhomogeneousInteraction]
        congr 1
        ring
  have hpath := rectangularPrismTransferPathWeight_eq_exp 1 beta
    (2 * n + 1) (2 * n + 1) n q
  have hexp := rectangularPrismPlusExponent_eq_layers 1 beta sigma
  have hord : a (q 0) *
        (∏ z : Fin (2 * n), A (q z.castSucc) (q z.succ)) *
        a (q (Fin.last (2 * n))) =
      Real.exp (-beta * rectangularPrismPlusEnergy 1 sigma) := by
    exact hpath.trans (congrArg Real.exp hexp.symm)
  unfold oddPrismFullTiltedPathWeight
  rw [oddPrismFullTiltedTransitionProduct_eq_ordinary_mul_exp
    beta n hn r sigma]
  rw [hw, ← hord]
  ring


end
end StatMech.FrontierA
