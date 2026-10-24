/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/MatchingCharacterization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace MatchingPolytope

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def IsMatchingSet (M : Set (Sym2 V)) : Prop :=
  M ⊆ G.edgeSet ∧ ∀ e₁ ∈ M, ∀ e₂ ∈ M, ∀ v : V, v ∈ e₁ → v ∈ e₂ → e₁ = e₂
