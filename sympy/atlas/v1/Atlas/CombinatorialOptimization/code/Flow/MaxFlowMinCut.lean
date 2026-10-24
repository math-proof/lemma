/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/MaxFlowMinCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.CombinatorialOptimization.code.Flow.FlowCutBound
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Flow.FlowCutBound

open Finset BigOperators Classical

noncomputable section

namespace NetworkFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

def resCap' (N : FlowNetwork V) (fl : STFlow N) (u v : V) : ℝ :=
  N.cap u v - fl.f u v + fl.f v u

def resAdj' (N : FlowNetwork V) (fl : STFlow N) (u v : V) : Prop :=
  resCap' N fl u v > 0

def ResReachable (N : FlowNetwork V) (fl : STFlow N) (v : V) : Prop :=
  Relation.ReflTransGen (resAdj' N fl) N.s v

def NoAugmentingPath (N : FlowNetwork V) (fl : STFlow N) : Prop :=
  ¬ ResReachable N fl N.t

def resReachableSet (N : FlowNetwork V) (fl : STFlow N) : Finset V :=
  Finset.univ.filter (fun v => ResReachable N fl v)

lemma mem_resReachableSet_iff (N : FlowNetwork V) (fl : STFlow N) (v : V) :
    v ∈ resReachableSet N fl ↔ ResReachable N fl v := by
  simp [resReachableSet]

lemma s_mem_resReachableSet (N : FlowNetwork V) (fl : STFlow N) :
    N.s ∈ resReachableSet N fl := by
  rw [mem_resReachableSet_iff]
  exact Relation.ReflTransGen.refl

lemma t_not_mem_resReachableSet (N : FlowNetwork V) (fl : STFlow N) (hmax : NoAugmentingPath N fl) :
    N.t ∉ resReachableSet N fl := by
  rw [mem_resReachableSet_iff]
  exact hmax

def maxFlowCut (N : FlowNetwork V) (fl : STFlow N) (hmax : NoAugmentingPath N fl) :
    STCut N :=
  ⟨resReachableSet N fl, s_mem_resReachableSet N fl, t_not_mem_resReachableSet N fl hmax⟩
