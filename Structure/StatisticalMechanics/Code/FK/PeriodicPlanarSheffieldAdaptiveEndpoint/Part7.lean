/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part27
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAdaptiveEndpoint.Part8
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


structure PeriodicPlanarDualPair.CrossNestedOutwardEndpointCertificate
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) where
  preparation : D.CrossNestedOutwardArrayPreparation mu
  verticalStart : Tendsto (fun n => mu.real
    (D.primalEmbedding.verticalCrossingEvent
      ((preparation.array.chain n).level 0).raw.data.wideLeft
      ((preparation.array.chain n).level 0).raw.data.wideRight 0
      ((preparation.array.chain n).extentY 0))) atTop (nhds 1)
  horizontalEnd : Tendsto (fun n => mu.real
    (D.primalEmbedding.horizontalCrossingEvent 0
      ((preparation.array.chain n).extentX (2 * (n + 1) + 2)) 0
      ((preparation.array.chain n).extentY (2 * (n + 1) + 2))))
    atTop (nhds 1)


end StatMech.FK.PeriodicPlanar
