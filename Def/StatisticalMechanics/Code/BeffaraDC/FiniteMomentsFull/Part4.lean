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
import Theorem.StatisticalMechanics.Code.BeffaraDC.FiniteMomentsFull.Part3
open scoped BigOperators
open MeasureTheory


namespace StatMech

namespace BeffaraDC

open StatMech.FK StatMech

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def fkClusterSizeDomination {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (x : V) {C r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hbtail : ∀ N, fkClusterSizeTail G p 1 x N ≤ C * r ^ N) :
    ClusterSizeDomination :=
  clusterSizeDomination_of_geometricTail
    (dist := fun N => fkClusterSizeTail G p q x N) (C := C) (r := r)
    (fun N => fkClusterSizeTail_nonneg G p q x N) hr0 hr1
    (fkClusterSizeTail_geometricTail G hp hp1 hq x hbtail)

end BeffaraDC
end StatMech
