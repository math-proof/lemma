/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAspectComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAdaptiveEndpoint.Part9
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCrossingGluing.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarStrictCriticalAssembly
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarStrictNoCoexistenceClosure.Part2
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAspectComparison
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


noncomputable def PeriodicPlanarDualPair.CrossNestedOutwardAspectGluing.toPowerComparison
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (gluing : D.CrossNestedOutwardAspectGluing mu) :
    D.CrossNestedOutwardPowerAspectComparison mu := by
  refine {
    exponent := gluing.exponent
    horizontalEnd_ge_verticalStart_pow := ?_ }
  intro preparation n
  let source := mu.real (D.primalEmbedding.verticalCrossingEvent
    ((preparation.array.chain n).level 0).raw.data.wideLeft
    ((preparation.array.chain n).level 0).raw.data.wideRight 0
    ((preparation.array.chain n).extentY 0))
  calc
    source ^ gluing.exponent n =
        source ^ (gluing.events preparation n).length := by
      rw [gluing.length_events preparation n]
    _ <= mu.real (finiteEventIntersection (gluing.events preparation n)) :=
      finiteEventIntersection_measureReal_ge_pow mu hFKG source
        measureReal_nonneg (gluing.events preparation n)
        (gluing.measurable preparation n)
        (gluing.increasing preparation n)
        (gluing.source_le preparation n)
    _ <= mu.real (D.primalEmbedding.horizontalCrossingEvent 0
        ((preparation.array.chain n).extentX (2 * (n + 1) + 2)) 0
        ((preparation.array.chain n).extentY (2 * (n + 1) + 2))) :=
      measureReal_mono (gluing.glues preparation n)


end StatMech.FK.PeriodicPlanar
