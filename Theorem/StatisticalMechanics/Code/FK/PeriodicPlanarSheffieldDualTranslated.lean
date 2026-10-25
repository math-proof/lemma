/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualTranslated.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldTransverseAssembly
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDualTranslated
open MeasureTheory Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


theorem PeriodicGraph.translatedFiniteInfinitePairConnectionEvent_measurableSet
    (P : PeriodicGraph V) (z : Site 2) (L R : Finset V) (N : Nat) :
    MeasurableSet (P.translatedFiniteInfinitePairConnectionEvent z L R N) :=
  P.translateEvent_measurableSet z
    (P.finiteInfinitePairConnectionEvent_measurableSet L R N)


theorem PeriodicGraph.translatedFiniteInfinitePairConnectionEvent_measureReal
    (P : PeriodicGraph V)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (hTI : P.IsTranslationInvariant mu)
    (z : Site 2) (L R : Finset V) (N : Nat) :
    mu.real (P.translatedFiniteInfinitePairConnectionEvent z L R N) =
      mu.real (P.finiteInfinitePairConnectionEvent L R N) := by
  exact congrArg ENNReal.toReal
    (P.translateEvent_measure_eq mu hTI z
      (P.finiteInfinitePairConnectionEvent_measurableSet L R N))


end StatMech.FK.PeriodicPlanar
