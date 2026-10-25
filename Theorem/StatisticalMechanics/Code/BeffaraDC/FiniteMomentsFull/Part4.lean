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
import Def.StatisticalMechanics.Code.BeffaraDC.FiniteMomentsFull.Part4
open scoped BigOperators
open MeasureTheory


namespace StatMech

namespace BeffaraDC

open StatMech.FK StatMech

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


@[simp] theorem fkClusterSizeDomination_dist {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 1 ≤ q) (x : V) {C r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hbtail : ∀ N, fkClusterSizeTail G p 1 x N ≤ C * r ^ N) :
    (fkClusterSizeDomination G hp hp1 hq x hr0 hr1 hbtail).dist
      = fun N => fkClusterSizeTail G p q x N := rfl


theorem fkClusterSizeMoment_lt_top {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (x : V) {C r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hbtail : ∀ N, fkClusterSizeTail G p 1 x N ≤ C * r ^ N) (d : ℕ) :
    clusterMoment (fun N => fkClusterSizeTail G p q x N) d
      ≤ ∑' N : ℕ, (N : ℝ) ^ d * (C * r ^ N) := by
  have h := (fkClusterSizeDomination G hp hp1 hq x hr0 hr1 hbtail).allMoments_lt_top d
  simpa using h


theorem fkClusterSizeMoment_nonneg (p q : ℝ) (x : V) (d : ℕ) :
    0 ≤ clusterMoment (fun N => fkClusterSizeTail G p q x N) d :=
  clusterMoment_nonneg (fun N => fkClusterSizeTail_nonneg G p q x N) d


theorem bernoulliClusterSizeMoment_lt_top {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (x : V) {C r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hbtail : ∀ N, fkClusterSizeTail G p 1 x N ≤ C * r ^ N) (d : ℕ) :
    clusterMoment (fun N => fkClusterSizeTail G p 1 x N) d
      ≤ ∑' N : ℕ, (N : ℝ) ^ d * (C * r ^ N) :=
  fkClusterSizeMoment_lt_top G hp hp1 le_rfl x hr0 hr1 hbtail d

end BeffaraDC
end StatMech
