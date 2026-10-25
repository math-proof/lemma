/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/ShortestAugPathPhase.lean -/

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

def augPathLengths (G : SimpleGraph V) (M : G.Subgraph) : Set ℕ∞ :=
  { n : ℕ∞ | ∃ (u v : V) (p : G.Walk u v), p.IsAugmentingPath M ∧ (p.length : ℕ∞) = n }

noncomputable def shortestAugPathLength (G : SimpleGraph V) (M : G.Subgraph) : ℕ∞ :=
  sInf (augPathLengths G M)

end SimpleGraph
