module
public import Def.v1.Atlas.CombinatorialOptimization.code.Flow.FlowDecomposition.Part3
public import Theorem.Finset.Atlas.v1.CombinatorialOptimization.code.Flow.FlowDecomposition
public import Theorem.Finset.Atlas.v1.CombinatorialOptimization.code.Flow.ResidualGraph
public import Def.v1.Atlas.CombinatorialOptimization.code.Flow.ResidualGraph.Part2
public import Def.v1.Atlas.CombinatorialOptimization.code.Flow.LargeAugPath
open Finset BigOperators Classical


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/LargeAugPath.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace NetworkFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma max_sub_max_neg (a : ℝ) : max a 0 - max (-a) 0 = a := by
  by_cases h : a ≤ 0
  · have hna : (0 : ℝ) ≤ -a := by linarith
    rw [max_eq_right h, max_eq_left hna]
    ring
  · push_neg at h
    have hna : -a ≤ (0 : ℝ) := by linarith
    rw [max_eq_left (le_of_lt h), max_eq_right hna]
    ring

end NetworkFlow
