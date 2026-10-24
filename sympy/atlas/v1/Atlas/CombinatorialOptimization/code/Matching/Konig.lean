/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/Konig.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.CombinatorialOptimization.code.Matching.ForestCharacterization
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Matching.ForestCharacterization

open SimpleGraph Set

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

noncomputable def matchingNum (G : SimpleGraph V) : ℕ∞ :=
  ⨆ (M : G.Subgraph) (_ : M.IsMatching), M.edgeSet.encard

def alternatingForestSet (G : SimpleGraph V) (M : G.Subgraph) (A : Set V) : Set V :=
  {v | IsInAlternatingForest G M A v}

def konigCover (G : SimpleGraph V) (M : G.Subgraph) (A B : Set V) : Set V :=
  (A \ alternatingForestSet G M A) ∪ (B ∩ alternatingForestSet G M A)
