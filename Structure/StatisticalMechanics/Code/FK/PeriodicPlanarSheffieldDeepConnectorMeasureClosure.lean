/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDeepConnectorMeasureClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDeepConnectorCage
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDeepConnectorMeasureClosure
open Filter MeasureTheory Set


namespace StatMech.FK.PeriodicPlanar

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

namespace PeriodicPlanarDualPair

structure FiniteDeepConnectorBandSchedule
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (rDual : Real) (band : Nat) where
  rPrimal : Nat → Real
  Rdeep : Nat → Real
  cArm : Nat → Real
  dArm : Nat → Real
  width : Nat → Nat
  lower : Nat → Finset V
  upper : Nat → Finset V
  tendsto_one : Tendsto (fun n => mu.real
    (D.primalEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent
      (rPrimal n) (Rdeep n) (cArm n) (dArm n)
        (width n) (lower n) (upper n))) atTop (nhds 1)
  disjoint_band : ∀ n, Disjoint
    (D.primalEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent
      (rPrimal n) (Rdeep n) (cArm n) (dArm n)
        (width n) (lower n) (upper n))
    ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster
        rDual (-(band : Real)) band)


end PeriodicPlanarDualPair
end StatMech.FK.PeriodicPlanar
