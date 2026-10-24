/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/LargeAugPath.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.CombinatorialOptimization.code.Flow.FlowDecomposition
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Flow.FlowDecomposition
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Flow.ResidualGraph
import sympy.atlas.v1.Atlas.CombinatorialOptimization.code.Flow.ResidualGraph

open Finset BigOperators Classical

namespace NetworkFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

def IsMaxFlow (N : FlowNetwork V) (fl : STFlow N) : Prop :=
  ∀ fl' : STFlow N, flowValue N fl' ≤ flowValue N fl

noncomputable def edgeCount (N : FlowNetwork V) : ℕ :=
  (Finset.univ.filter (fun e : V × V => N.cap e.1 e.2 > 0)).card

lemma max_sub_max_neg (a : ℝ) : max a 0 - max (-a) 0 = a := by
  by_cases h : a ≤ 0
  · have hna : (0 : ℝ) ≤ -a := by linarith
    rw [max_eq_right h, max_eq_left hna]
    ring
  · push_neg at h
    have hna : -a ≤ (0 : ℝ) := by linarith
    rw [max_eq_left (le_of_lt h), max_eq_right hna]
    ring

noncomputable def residualNetwork (N : FlowNetwork V) (fl : STFlow N) : FlowNetwork V :=
  { s := N.s
    t := N.t
    s_ne_t := N.s_ne_t
    cap := fun u v => resCap N fl u v
    cap_nonneg := fun u v => resCap_nonneg N fl u v }

noncomputable def diffFlowFun (N : FlowNetwork V) (fl fl_max : STFlow N) (u v : V) : ℝ :=
  max (fl_max.f u v - fl.f u v) 0 + max (fl.f v u - fl_max.f v u) 0

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

noncomputable def diffFlow (N : FlowNetwork V) (fl fl_max : STFlow N) :
    STFlow (residualNetwork N fl) :=
  { f := diffFlowFun N fl fl_max
    flow_nonneg := diffFlowFun_nonneg N fl fl_max
    flow_cap := diffFlowFun_le_resCap N fl fl_max
    conservation := diffFlowFun_conservation N fl fl_max }
