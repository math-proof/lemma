/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoverage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarDualPair.Part3
import Theorem.StatisticalMechanics.Code.FK.TriHexCriticalReduction.Part5
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarCoverage
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


theorem PeriodicGraph.bufferedTwoPointEvent_isIncreasing
    (P : PeriodicGraph V) (N : ℕ) (x y : P.BufferedVertex N) :
    IsIncreasing (P.bufferedTwoPointEvent N x y) := by
  intro omega eta home hreach
  exact hreach.mono fun u v huv => by
    rw [FK.openSub_adj] at huv ⊢
    refine ⟨huv.1, Bool.eq_true_of_true_le ?_⟩
    simpa [huv.2] using home s(u, v)


end StatMech.FK.PeriodicPlanar
