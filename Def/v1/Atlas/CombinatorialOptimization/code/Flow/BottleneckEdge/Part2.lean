/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/BottleneckEdge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.CombinatorialOptimization.code.Flow.ShortestAugPath
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Flow.ShortestAugPath
import Structure.v1.Atlas.CombinatorialOptimization.code.Flow.BottleneckEdge
open Finset BigOperators Classical


namespace NetworkFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def bottleneckCount (N : FlowNetwork V) {k : ℕ}
    (seq : ShortestAugSeq N k) (u v : V) : ℕ :=
  Finset.card (Finset.filter (fun i : Fin k =>
    ∃ (p : List V) (hp : IsShortestAugmentingPath N (seq.fl i.castSucc) p),
      IsBottleneckEdge N (seq.fl i.castSucc) p hp u v)
    Finset.univ)

end NetworkFlow
