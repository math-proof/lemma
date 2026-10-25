/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/FlowDecomposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.CombinatorialOptimization.code.Flow.FlowCutBound.Part2
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Flow.FlowCutBound
import Def.v1.Atlas.CombinatorialOptimization.code.Flow.FlowDecomposition.Part2
open Finset BigOperators Classical


namespace NetworkFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

instance FlowPath.decidable_mem_edges {N : FlowNetwork V} (p : FlowPath N) (u v : V) :
    Decidable (p.mem_edges u v) := by
  unfold mem_edges edges; exact inferInstance

end NetworkFlow
