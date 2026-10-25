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
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAspectComparison.Part2
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


structure PeriodicPlanarDualPair.CrossNestedOutwardPowerAspectComparison
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) where
  exponent : Nat -> Nat
  horizontalEnd_ge_verticalStart_pow :
    forall (preparation : D.CrossNestedOutwardArrayPreparation mu) n,
      (mu.real (D.primalEmbedding.verticalCrossingEvent
        ((preparation.array.chain n).level 0).raw.data.wideLeft
        ((preparation.array.chain n).level 0).raw.data.wideRight 0
        ((preparation.array.chain n).extentY 0))) ^ exponent n <=
      mu.real (D.primalEmbedding.horizontalCrossingEvent 0
        ((preparation.array.chain n).extentX (2 * (n + 1) + 2)) 0
        ((preparation.array.chain n).extentY (2 * (n + 1) + 2)))


structure PeriodicPlanarDualPair.CrossNestedOutwardAspectGluing
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) where
  exponent : Nat -> Nat
  events : D.CrossNestedOutwardArrayPreparation mu -> Nat ->
    List (Set (ConfigSpace (Sym2 V)))
  length_events : forall preparation n,
    (events preparation n).length = exponent n
  measurable : forall preparation n A,
    A ∈ events preparation n -> MeasurableSet A
  increasing : forall preparation n A,
    A ∈ events preparation n -> IsIncreasing A
  source_le : forall preparation n A, A ∈ events preparation n ->
    mu.real (D.primalEmbedding.verticalCrossingEvent
      ((preparation.array.chain n).level 0).raw.data.wideLeft
      ((preparation.array.chain n).level 0).raw.data.wideRight 0
      ((preparation.array.chain n).extentY 0)) <= mu.real A
  glues : forall preparation n,
    finiteEventIntersection (events preparation n) <=
      D.primalEmbedding.horizontalCrossingEvent 0
        ((preparation.array.chain n).extentX (2 * (n + 1) + 2)) 0
        ((preparation.array.chain n).extentY (2 * (n + 1) + 2))


end StatMech.FK.PeriodicPlanar
