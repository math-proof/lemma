/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldMacroArrayAssembly.Part2
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldArrayClosure
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

theorem PeriodicPlaneEmbedding.CarriedCrossNestedArray.verticalCrossingLimit
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (data : E.CarriedCrossNestedArray mu) :
    Tendsto (fun n ↦ mu.real (E.verticalCrossingEvent
      (data.aWide n) (data.bWide n) (data.c n) (data.d n)))
      atTop (nhds 1) :=
  E.verticalCrossing_tendsto_one_of_carriedComponents mu hFKG
    data.a data.b data.c data.d data.aWide data.bWide
    data.bottom data.top data.verticalRadius data.wideLeft data.wideRight
    data.verticalConnector data.bottomLimit data.topLimit
    data.verticalMergeLimit

theorem PeriodicPlaneEmbedding.CarriedCrossNestedArray.horizontalCrossingLimit
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (data : E.CarriedCrossNestedArray mu) :
    Tendsto (fun n ↦ mu.real (E.horizontalCrossingEvent
      (data.a n) (data.b n) (data.cTall n) (data.dTall n)))
      atTop (nhds 1) :=
  E.horizontalCrossing_tendsto_one_of_carriedComponents mu hFKG
    data.a data.b data.c data.d data.cTall data.dTall
    data.left data.right data.horizontalRadius data.tallBottom data.tallTop
    data.horizontalConnector data.leftLimit data.rightLimit
    data.horizontalMergeLimit

theorem PeriodicPlaneEmbedding.CarriedCrossNestedArray.crossingMaxLimit
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (data : E.CarriedCrossNestedArray mu) :
    Tendsto (fun n ↦ max
      (mu.real (E.horizontalCrossingEvent
        (data.a n) (data.b n) (data.cTall n) (data.dTall n)))
      (mu.real (E.verticalCrossingEvent
        (data.aWide n) (data.bWide n) (data.c n) (data.d n))))
      atTop (nhds 1) := by
  simpa only [max_self] using
    (data.horizontalCrossingLimit E mu hFKG).max
      (data.verticalCrossingLimit E mu hFKG)


end StatMech.FK.PeriodicPlanar
