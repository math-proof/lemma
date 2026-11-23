/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/ResidualGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Def.v1.Atlas.CombinatorialOptimization.code.Flow.FlowCutBound.Part2
public import Theorem.Finset.Atlas.v1.CombinatorialOptimization.code.Flow.FlowCutBound
public import Def.v1.Atlas.CombinatorialOptimization.code.Flow.ResidualGraph
open Finset BigOperators

public section

namespace NetworkFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma resCap_nonneg (N : FlowNetwork V) (fl : STFlow N) (u v : V) :
    0 ≤ resCap N fl u v := by
  unfold resCap
  linarith [fl.flow_nonneg v u, fl.flow_cap u v]

end NetworkFlow
