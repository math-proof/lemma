/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneStrip.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneTranslation.Part2
open Filter MeasureTheory Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

theorem PeriodicGraph.setConnectionWithin_mono_region
    (P : PeriodicGraph V) {A B : Set V} (hAB : A ⊆ B) (S T : Set V) :
    P.setConnectionWithin A S T ⊆ P.setConnectionWithin B S T := by
  rintro omega ⟨x, hx, y, hy, hxy⟩
  exact ⟨x, hx, y, hy, P.connectedWithinSet_mono_region hAB x y hxy⟩


end StatMech.FK.PeriodicPlanar
