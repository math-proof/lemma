/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/BlossomShrinking.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.CombinatorialOptimization.code.Matching.Berge
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Matching.Berge
import Def.v1.Atlas.CombinatorialOptimization.code.Matching.BlossomShrinking
open SimpleGraph


namespace SimpleGraph

variable {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

structure IsBlossom (G : SimpleGraph V) (M : G.Subgraph) (B : Finset V) (base : V) : Prop where
  base_mem : base ∈ B
  card_odd : Odd B.card
  card_ge : B.card ≥ 3
  cycle_exists : ∃ (c : G.Walk base base), c.IsCycle ∧ c.support.toFinset = B
  matched_internal : ∀ v ∈ B, v ≠ base → ∃ w ∈ B, w ≠ v ∧ M.Adj v w
  stem : ∃ w, w ∉ B ∧ M.Adj base w

end SimpleGraph
