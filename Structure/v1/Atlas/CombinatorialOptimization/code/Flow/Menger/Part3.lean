/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/Menger.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.CombinatorialOptimization.code.Flow.MaxFlowMinCut.Part2
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Flow.MaxFlowMinCut
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Flow.MaxFlowAugPath
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Flow.FlowDecomposition
import Instance.v1.Atlas.CombinatorialOptimization.code.Flow.MaxFlowAugPath
import Def.v1.Atlas.CombinatorialOptimization.code.Flow.FlowDecomposition.Part3
import Def.v1.Atlas.CombinatorialOptimization.code.Flow.Menger
open Finset BigOperators Classical


noncomputable section

namespace NetworkFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

structure EdgeDisjointPaths (G : DirectedGraph V) (k : ℕ) where
  paths : Fin k → DirPath G
  disjoint : PairwiseEdgeDisjoint paths

end NetworkFlow
end
