/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/FiniteMomentsFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.StochasticDomination
import Theorem.StatisticalMechanics.Code.FK.TwoPoint.Part4
import Theorem.StatisticalMechanics.Code.FK.ComparisonHolley.Part3
import Theorem.StatisticalMechanics.Code.FK.HolleyCoupling.Part2
import Theorem.StatisticalMechanics.Code.BeffaraDC.ClusterMoments.Part3
import Def.StatisticalMechanics.Code.BeffaraDC.FiniteMomentsFull.Part2
open scoped BigOperators
open MeasureTheory


namespace StatMech

namespace BeffaraDC

open StatMech.FK StatMech

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem fkClusterSizeLargeEvent_isIncreasing (x : V) (N : ℕ) :
    IsIncreasing (fkClusterSizeLargeEvent G x N) := by
  intro a b hab ha
  simp only [fkClusterSizeLargeEvent, Set.mem_setOf_eq] at ha ⊢
  exact ha.trans (Finset.card_le_card (fkCluster_mono G hab x))


theorem measurableSet_fkClusterSizeLargeEvent (x : V) (N : ℕ) :
    MeasurableSet (fkClusterSizeLargeEvent G x N) :=
  DiscreteMeasurableSpace.forall_measurableSet (fkClusterSizeLargeEvent G x N)


end BeffaraDC
end StatMech
