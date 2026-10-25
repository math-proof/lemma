/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/MaxFlowMinCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.CombinatorialOptimization.code.Flow.FlowCutBound.Part2
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Flow.FlowCutBound
import Def.v1.Atlas.CombinatorialOptimization.code.Flow.MaxFlowMinCut
open Finset BigOperators Classical


noncomputable section

namespace NetworkFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

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

end NetworkFlow
end
