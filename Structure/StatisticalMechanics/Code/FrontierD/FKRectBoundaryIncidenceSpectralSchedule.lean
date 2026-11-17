/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceSpectralSchedule.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBalancedShareVerticalRate
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectAllSectorWidthRate
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceRateCapstone
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidencePIMSSchedule.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidencePIMSPhaseAssembly
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceSpectralSchedule.Part3
open Filter Topology MeasureTheory


namespace StatMech.FrontierD

open StatMech.FK StatMech.Lattice StatMech.Percolation StatMech.BeffaraDC

public noncomputable section

structure FKQgt4BoundaryIncidenceScheduledSpectralGap
    (q xiInv : Real) : Prop where
  winding : forall r : Nat, 2 <= r -> forall m : Nat -> Nat,
    (forall k, fkRectBoundaryIncidencePIMSHeightLower q r k <= m k) ->
    Tendsto (fun k =>
      -Real.log
          (fkRectCriticalWindingTailMass
            (fkRectFixedChargeVerticalFamily r k (m k)) q r) /
        (fkRectFixedChargeVerticalFamily r k (m k)).height)
      atTop (nhds (((r - 1 : Nat) : Real) * xiInv))
  spectralGap : forall r : Nat, 2 <= r ->
    Tendsto (fkRectBalancedShareSpectralGap q r) atTop (nhds 0)


end
end StatMech.FrontierD
