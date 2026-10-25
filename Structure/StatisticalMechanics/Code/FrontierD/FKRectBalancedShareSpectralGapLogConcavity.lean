/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedShareSpectralGapLogConcavity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceSpectralSchedule.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveEvenTraceLogConcavity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBalancedShareSpectralGapLogConcavity.Part2
open Filter MeasureTheory Topology


namespace StatMech.FrontierD

open StatMech.FK StatMech.Lattice StatMech.Percolation StatMech.BeffaraDC

noncomputable section

structure FKQgt4BoundaryIncidenceScheduledWindingTraceLogConcavity
    (q xiInv : Real) : Prop where
  winding : forall r : Nat, 2 <= r -> forall m : Nat -> Nat,
    (forall k, fkRectBoundaryIncidencePIMSHeightLower q r k <= m k) ->
    Tendsto (fun k =>
      -Real.log
          (fkRectCriticalWindingTailMass
            (fkRectFixedChargeVerticalFamily r k (m k)) q r) /
        (fkRectFixedChargeVerticalFamily r k (m k)).height)
      atTop (nhds (((r - 1 : Nat) : Real) * xiInv))
  traceLogConcavity : forall r : Nat, 2 <= r -> forall k : Nat,
    SixVertexSectorTraceLogConcave
      (sixVertexFourWidth r (k + 1)) (fkQgt4SixVertexWeight q)


end
end StatMech.FrontierD
