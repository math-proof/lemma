/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/EdmondsProgress.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.CombinatorialOptimization.code.Matching.BlossomShrinking.Part2
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Matching.BlossomShrinking
import Structure.v1.Atlas.CombinatorialOptimization.code.Matching.EdmondsProgress
open SimpleGraph


namespace SimpleGraph

variable {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

def AlternatingForest.isEvenLevel (F : AlternatingForest G M) (v : V) : Prop :=
  v ∈ F.forestVerts ∧ Even (F.level v)

end SimpleGraph
