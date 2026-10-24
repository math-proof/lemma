/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/EdmondsProgress.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.CombinatorialOptimization.code.Matching.BlossomShrinking
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Matching.BlossomShrinking

open SimpleGraph

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

structure AlternatingForest (G : SimpleGraph V) (M : G.Subgraph) where
  forestVerts : Finset V
  root : V → V
  level : V → ℕ
  roots_unmatched : ∀ v ∈ forestVerts, level v = 0 → v ∉ M.verts
  root_mem : ∀ v ∈ forestVerts, root v ∈ forestVerts
  root_level : ∀ v ∈ forestVerts, level (root v) = 0
  root_self : ∀ v ∈ forestVerts, root v = v ↔ level v = 0
  odd_level_matched : ∀ v ∈ forestVerts, Odd (level v) → v ∈ M.verts
  unmatched_are_roots : ∀ v, v ∉ M.verts → v ∈ forestVerts
  unmatched_level_zero : ∀ v ∈ forestVerts, v ∉ M.verts → level v = 0
  matched_partner_even : ∀ v ∈ forestVerts, Odd (level v) →
    ∀ w, M.Adj v w → w ∈ forestVerts ∧ Even (level w) ∧ root w = root v

def AlternatingForest.isEvenLevel (F : AlternatingForest G M) (v : V) : Prop :=
  v ∈ F.forestVerts ∧ Even (F.level v)
