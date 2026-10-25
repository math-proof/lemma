/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/MaxFlowMinCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.CombinatorialOptimization.code.Flow.FlowCutBound.Part2
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Flow.FlowCutBound
import Theorem.v1.Atlas.CombinatorialOptimization.code.Flow.MaxFlowMinCut
open Finset BigOperators Classical


noncomputable section

namespace NetworkFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

def maxFlowCut (N : FlowNetwork V) (fl : STFlow N) (hmax : NoAugmentingPath N fl) :
    STCut N :=
  ⟨resReachableSet N fl, s_mem_resReachableSet N fl, t_not_mem_resReachableSet N fl hmax⟩

end NetworkFlow
end
