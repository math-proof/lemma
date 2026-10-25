/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceSpectralSchedule.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBalancedShareVerticalRate
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectAllSectorWidthRate
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceRateCapstone
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidencePIMSSchedule.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidencePIMSPhaseAssembly
open Filter Topology MeasureTheory


namespace StatMech.FrontierD

open StatMech.FK StatMech.Lattice StatMech.Percolation StatMech.BeffaraDC

noncomputable section

theorem exists_nat_uniform_lower_tendsto_above
    (f : Nat -> Nat -> Real) (a : Nat -> Real) {L : Real}
    (prescribed : Nat -> Nat)
    (hvertical : forall k, Tendsto (f k) atTop (nhds (a k)))
    (hhorizontal : Tendsto a atTop (nhds L)) :
    exists lower : Nat -> Nat,
      (forall k, prescribed k <= lower k) /\
      forall m : Nat -> Nat, (forall k, lower k <= m k) ->
        Tendsto (fun k => f k (m k)) atTop (nhds L) := by
  have hchoose (k : Nat) : exists M : Nat, forall n : Nat, M <= n ->
      dist (f k n) (a k) < (1 : Real) / (k + 1) := by
    have heps : 0 < (1 : Real) / (k + 1) := by positivity
    have hev : ∀ᶠ n in atTop,
        f k n ∈ Metric.ball (a k) ((1 : Real) / (k + 1)) :=
      hvertical k (Metric.ball_mem_nhds _ heps)
    obtain ⟨M, hM⟩ := eventually_atTop.1 hev
    exact ⟨M, fun n hn => by
      simpa only [Metric.mem_ball] using hM n hn⟩
  choose M hM using hchoose
  let lower : Nat -> Nat := fun k => max (prescribed k) (M k)
  refine ⟨lower, fun k => le_max_left _ _, ?_⟩
  intro m hm
  have herr (k : Nat) :
      dist (f k (m k)) (a k) <= (1 : Real) / (k + 1) := by
    exact (hM k (m k) ((le_max_right _ _).trans (hm k))).le
  have heps : Tendsto (fun k : Nat => (1 : Real) / (k + 1))
      atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have haDist : Tendsto (fun k => dist (a k) L) atTop (nhds 0) :=
    (tendsto_iff_dist_tendsto_zero).1 hhorizontal
  have hdist : Tendsto (fun k => dist (f k (m k)) L)
      atTop (nhds 0) := by
    apply squeeze_zero (g := fun k =>
      (1 : Real) / (k + 1) + dist (a k) L)
    · exact fun _ => dist_nonneg
    · intro k
      calc
        dist (f k (m k)) L <=
            dist (f k (m k)) (a k) + dist (a k) L :=
          dist_triangle _ _ _
        _ <= (1 : Real) / (k + 1) + dist (a k) L := by
          exact add_le_add (herr k) le_rfl
    · simpa using heps.add haDist
  exact (tendsto_iff_dist_tendsto_zero).2 hdist


end
end StatMech.FrontierD
