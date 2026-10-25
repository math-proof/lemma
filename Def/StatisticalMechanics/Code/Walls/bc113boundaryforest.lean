/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc113boundaryforest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc113boundaryforest
open Set SimpleGraph Finset

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option maxRecDepth 4000


namespace StatMech.Walls

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def bc113_toB (G : SimpleGraph V) (B : V → Prop) (v : V) : ℕ := by
  classical
  exact if h : ∃ b, B b ∧ G.Reachable v b then
    (Finset.univ.filter (fun b => B b ∧ G.Reachable v b)).inf'
      (by
        obtain ⟨b, hb⟩ := h
        exact ⟨b, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hb⟩)
      (fun b => G.dist v b)
  else 0


def bc113_ReachesB (G : SimpleGraph V) (B : V → Prop) : Prop :=
  ∀ v, ∃ b, B b ∧ G.Reachable v b


end StatMech.Walls
