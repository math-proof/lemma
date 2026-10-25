/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/FlowDecomposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.CombinatorialOptimization.code.Flow.FlowCutBound.Part2
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Flow.FlowCutBound
import Def.v1.Atlas.CombinatorialOptimization.code.Flow.FlowDecomposition
open Finset BigOperators Classical


namespace NetworkFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

structure FlowPath (N : FlowNetwork V) where
  vertices : List V
  nonempty : vertices ≠ []
  starts_at_s : vertices.head nonempty = N.s
  ends_at_t : vertices.getLast nonempty = N.t
  length_ge_two : vertices.length ≥ 2
  nodup : vertices.Nodup

end NetworkFlow
