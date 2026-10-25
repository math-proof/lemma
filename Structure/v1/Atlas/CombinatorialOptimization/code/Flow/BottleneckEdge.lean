/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/BottleneckEdge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.CombinatorialOptimization.code.Flow.ShortestAugPath
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Flow.ShortestAugPath
import Def.v1.Atlas.CombinatorialOptimization.code.Flow.BottleneckEdge
open Finset BigOperators Classical


namespace NetworkFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

structure ShortestAugSeq (N : FlowNetwork V) (k : ℕ) where
  fl : Fin (k + 1) → STFlow N
  augments : ∀ i : Fin k, IsShortestPathAugmentation N (fl i.castSucc) (fl i.succ)

end NetworkFlow
