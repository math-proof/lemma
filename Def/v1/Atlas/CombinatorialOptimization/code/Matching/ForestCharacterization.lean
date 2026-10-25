/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/ForestCharacterization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.CombinatorialOptimization.code.Matching.Berge
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Matching.Berge
open SimpleGraph


namespace SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def IsInAlternatingForest (G : SimpleGraph V) (M : G.Subgraph) (A : Set V) (b : V) : Prop :=
  ∃ (a : V) (p : G.Walk a b), a ∈ A ∧ a ∉ M.verts ∧ p.IsPath ∧ p.IsAlternatingFrom M

end SimpleGraph
