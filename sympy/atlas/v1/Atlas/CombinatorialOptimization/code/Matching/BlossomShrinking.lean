/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/BlossomShrinking.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.CombinatorialOptimization.code.Matching.Berge
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Matching.Berge

open SimpleGraph

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

def blossomContractMap (B : Finset V) (base : V) : V → V :=
  fun v => if v ∈ B then base else v

def contractBlossom (G : SimpleGraph V) (B : Finset V) (base : V) : SimpleGraph V :=
  G.map (blossomContractMap B base)

structure IsBlossom (G : SimpleGraph V) (M : G.Subgraph) (B : Finset V) (base : V) : Prop where
  base_mem : base ∈ B
  card_odd : Odd B.card
  card_ge : B.card ≥ 3
  cycle_exists : ∃ (c : G.Walk base base), c.IsCycle ∧ c.support.toFinset = B
  matched_internal : ∀ v ∈ B, v ≠ base → ∃ w ∈ B, w ≠ v ∧ M.Adj v w
  stem : ∃ w, w ∉ B ∧ M.Adj base w

def inducedMatchingSubgraph (M : G.Subgraph) (B : Finset V) (base : V) :
    (contractBlossom G B base).Subgraph where
  verts := (blossomContractMap B base) '' M.verts
  Adj u v := (contractBlossom G B base).Adj u v ∧
    ∃ a b, blossomContractMap B base a = u ∧ blossomContractMap B base b = v ∧
      M.Adj a b ∧ ¬(a ∈ B ∧ b ∈ B)
  adj_sub := fun ⟨hadj, _⟩ => hadj
  edge_vert := by
    intro u v ⟨_, a, _, hau, _, hadj_M, _⟩
    rw [← hau]
    exact Set.mem_image_of_mem (blossomContractMap B base) (M.edge_vert hadj_M)
  symm := by
    intro u v ⟨hadj, a, b, hau, hbv, hadj_M, hnotB⟩
    exact ⟨hadj.symm, b, a, hbv, hau, hadj_M.symm, fun ⟨hb, ha⟩ => hnotB ⟨ha, hb⟩⟩
