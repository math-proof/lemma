/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part20
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

structure PairedAdjacentBoundaryBandScheduleData
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (muDual : Measure (ConfigSpace (Sym2 W))) (step : Nat -> Int) where
  step_nonneg : forall n, 0 <= step n
  radius : Nat -> Nat
  radiusDual : Nat -> Nat
  score : Nat -> Real
  scoreDual : Nat -> Real
  family : forall m,
    E.NormalBoundaryBandFamily mu (P.orbitBox m) (score m)
  familyDual : forall m,
    Edual.NormalBoundaryBandFamily muDual
      (Pdual.orbitBox m) (scoreDual m)
  primalContinuation :
    E.UniformAdjacentBoundaryBandCrossingRadius mu step radius
  primalMerge : forall q : Nat -> Fin 2 × (Fin 3 × Fin 3),
    Tendsto (fun n => mu.real (P.pairMergeErrorUnion (P.orbitBox n)
      ((P.orbitBox n).image (P.shift
        (preferenceKingOffset (q n).2 +
          if (q n).1.val = 0 then 0 else verticalShift (step n))))
      (radius n))) atTop (nhds 0)
  dualContinuation : Edual.UniformBoundaryBandCrossingRadius
    muDual radiusDual
  score_tendsto : Tendsto score atTop (nhds 1)
  score_le_one : forall m, score m <= 1
  scoreDual_tendsto : Tendsto scoreDual atTop (nhds 1)
  scoreDual_le_one : forall m, scoreDual m <= 1
  schedule : forall m, PairedAlignedMarginSchedule E Edual
    (family m) (familyDual m)
    (fun _ => max
      (E.connectorMarginRequirement (radius m))
      (Edual.connectorMarginRequirement (radiusDual m)))
    (fun _ => max
      (E.connectorMarginRequirement (radius m))
      (Edual.connectorMarginRequirement (radiusDual m)))


end StatMech.FK.PeriodicPlanar
