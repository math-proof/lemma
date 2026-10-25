/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/BottleneckEdge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.CombinatorialOptimization.code.Flow.ShortestAugPath
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Flow.ShortestAugPath
open Finset BigOperators Classical


namespace NetworkFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

def IsBottleneckEdge (N : FlowNetwork V) (fl : STFlow N) (p : List V)
    (hp : IsShortestAugmentingPath N fl p) (u v : V) : Prop :=
  EdgeOnPath p u v ∧
  resCap N fl u v = pathBottleneck N fl p hp.1.1

end NetworkFlow
