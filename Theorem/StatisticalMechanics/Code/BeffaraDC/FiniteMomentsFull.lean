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
import Def.StatisticalMechanics.Code.BeffaraDC.FiniteMomentsFull
open scoped BigOperators
open MeasureTheory


namespace StatMech

namespace BeffaraDC

open StatMech.FK StatMech

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem fkCluster_mono {a b : ConfigSpace (Sym2 V)} (hab : a ≤ b) (x : V) :
    fkCluster G a x ⊆ fkCluster G b x := by
  intro y hy
  unfold fkCluster at hy ⊢
  rw [Finset.mem_filter] at hy ⊢
  exact ⟨hy.1, hy.2.mono (openSub_mono G hab)⟩


end BeffaraDC
end StatMech
