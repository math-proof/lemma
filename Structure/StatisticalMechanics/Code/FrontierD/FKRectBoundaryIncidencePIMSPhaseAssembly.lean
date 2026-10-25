/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidencePIMSPhaseAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidencePIMSSchedule.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4PIMSTwoByOnePhaseAssembly
open Filter MeasureTheory Topology


namespace StatMech.FrontierD

open StatMech.FK StatMech.Lattice StatMech.Percolation StatMech.BeffaraDC

noncomputable section

structure FKQgt4BoundaryIncidenceScheduledFourCopy
    (q xiInv : Real) : Prop where
  winding : forall r : Nat, 2 ≤ r -> forall m : Nat → Nat,
    (∀ k, fkRectBoundaryIncidencePIMSHeightLower q r k ≤ m k) ->
    Tendsto (fun k =>
      -Real.log
          (fkRectCriticalWindingTailMass
            (fkRectFixedChargeVerticalFamily r k (m k)) q r) /
        (fkRectFixedChargeVerticalFamily r k (m k)).height)
      atTop (nhds (((r - 1 : Nat) : Real) * xiInv))
  fourCopy : forall r : Nat, 2 ≤ r -> forall m : Nat → Nat,
    (∀ k, fkRectBoundaryIncidencePIMSHeightLower q r k ≤ m k) ->
    Tendsto (fun k =>
      fkRectFourCopyShareCost
          (fkRectFixedChargeVerticalFamily r k (m k)) q /
        (fkRectFixedChargeVerticalFamily r k (m k)).height)
      atTop (nhds 0)


end
end StatMech.FrontierD
