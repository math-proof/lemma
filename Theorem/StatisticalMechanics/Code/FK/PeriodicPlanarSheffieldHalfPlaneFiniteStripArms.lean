/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneFiniteStripArms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneJoinedArmsHighProbability.Part2
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

theorem PeriodicGraph.infiniteSetConnectionWithin_mono_region
    (P : PeriodicGraph V) {A B : Set V} (hAB : A ⊆ B) (S T : Set V) :
    P.infiniteSetConnectionWithin A S T ⊆
      P.infiniteSetConnectionWithin B S T := by
  rintro omega ⟨x, hx, hinf, y, hy, hxy⟩
  exact ⟨x, hx, hinf, y, hy,
    P.connectedWithinSet_mono_region hAB x y hxy⟩


end StatMech.FK.PeriodicPlanar
