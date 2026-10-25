/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/LargeAugPath.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.CombinatorialOptimization.code.Flow.FlowDecomposition.Part3
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Flow.FlowDecomposition
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Flow.ResidualGraph
import Def.v1.Atlas.CombinatorialOptimization.code.Flow.ResidualGraph.Part2
import Def.v1.Atlas.CombinatorialOptimization.code.Flow.LargeAugPath.Part2
open Finset BigOperators Classical


namespace NetworkFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma diffFlowFun_nonneg (N : FlowNetwork V) (fl fl_max : STFlow N) (u v : V) :
    0 ≤ diffFlowFun N fl fl_max u v := by
  unfold diffFlowFun; positivity

lemma diffFlowFun_le_resCap (N : FlowNetwork V) (fl fl_max : STFlow N) (u v : V) :
    diffFlowFun N fl fl_max u v ≤ resCap N fl u v := by
  unfold diffFlowFun resCap
  have h1 := fl_max.flow_cap u v
  have h2 := fl_max.flow_nonneg v u
  have h3 := fl.flow_nonneg u v
  have h4 := fl.flow_cap v u
  have h5 := fl.flow_cap u v
  have h6 := fl.flow_nonneg v u
  have hle1 : max (fl_max.f u v - fl.f u v) 0 ≤ N.cap u v - fl.f u v := by
    apply max_le <;> linarith
  have hle2 : max (fl.f v u - fl_max.f v u) 0 ≤ fl.f v u := by
    apply max_le <;> linarith
  linarith

lemma diffFlowFun_conservation (N : FlowNetwork V) (fl fl_max : STFlow N) (w : V)
    (hw_s : w ≠ N.s) (hw_t : w ≠ N.t) :
    ∑ u : V, diffFlowFun N fl fl_max u w = ∑ u : V, diffFlowFun N fl fl_max w u := by
  suffices h : ∑ u : V, diffFlowFun N fl fl_max u w -
      ∑ u : V, diffFlowFun N fl fl_max w u = 0 by linarith
  simp only [diffFlowFun]
  rw [show ∑ u : V, (max (fl_max.f u w - fl.f u w) 0 + max (fl.f w u - fl_max.f w u) 0) =
      ∑ u : V, max (fl_max.f u w - fl.f u w) 0 + ∑ u : V, max (fl.f w u - fl_max.f w u) 0
    from Finset.sum_add_distrib]
  rw [show ∑ u : V, (max (fl_max.f w u - fl.f w u) 0 + max (fl.f u w - fl_max.f u w) 0) =
      ∑ u : V, max (fl_max.f w u - fl.f w u) 0 + ∑ u : V, max (fl.f u w - fl_max.f u w) 0
    from Finset.sum_add_distrib]
  have eq1 : ∑ u : V, max (fl_max.f u w - fl.f u w) 0 -
             ∑ u : V, max (fl.f u w - fl_max.f u w) 0 =
             ∑ u : V, (fl_max.f u w - fl.f u w) := by
    rw [← Finset.sum_sub_distrib]
    congr 1; ext u
    have h2 : fl.f u w - fl_max.f u w = -(fl_max.f u w - fl.f u w) := by ring
    rw [h2]
    exact max_sub_max_neg (fl_max.f u w - fl.f u w)
  have eq2 : ∑ u : V, max (fl.f w u - fl_max.f w u) 0 -
             ∑ u : V, max (fl_max.f w u - fl.f w u) 0 =
             ∑ u : V, (fl.f w u - fl_max.f w u) := by
    rw [← Finset.sum_sub_distrib]
    congr 1; ext u
    have h2 : fl_max.f w u - fl.f w u = -(fl.f w u - fl_max.f w u) := by ring
    rw [h2]
    exact max_sub_max_neg (fl.f w u - fl_max.f w u)

  have cons_max := fl_max.conservation w hw_s hw_t
  have cons_fl := fl.conservation w hw_s hw_t
  linarith [Finset.sum_sub_distrib (s := Finset.univ)
              (f := fun u => fl_max.f u w) (g := fun u => fl.f u w),
            Finset.sum_sub_distrib (s := Finset.univ)
              (f := fun u => fl.f w u) (g := fun u => fl_max.f w u)]

end NetworkFlow
