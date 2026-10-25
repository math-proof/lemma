/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverage.Part3
import Theorem.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing.Part9
import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield.Part13
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


theorem PeriodicGraph.translateEvent_measurableSet
    (P : PeriodicGraph V) (z : Site 2)
    {A : Set (ConfigSpace (Sym2 V))} (hA : MeasurableSet A) :
    MeasurableSet (P.translateEvent z A) :=
  hA.preimage (P.measurable_configTranslate z)

theorem PeriodicGraph.translateEvent_isIncreasing
    (P : PeriodicGraph V) (z : Site 2)
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) :
    IsIncreasing (P.translateEvent z A) :=
  fun _ _ home hmem => hA (P.configTranslate_mono z home) hmem

theorem PeriodicGraph.translateEvent_measure_eq
    (P : PeriodicGraph V) (mu : Measure (ConfigSpace (Sym2 V)))
    (hTI : P.IsTranslationInvariant mu) (z : Site 2)
    {A : Set (ConfigSpace (Sym2 V))} (hA : MeasurableSet A) :
    mu (P.translateEvent z A) = mu A :=
  (hTI z).measure_preimage hA.nullMeasurableSet


end StatMech.FK.PeriodicPlanar
