/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc16core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc15core.Part5
import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc16core.Part2
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.show false
set_option linter.style.openClassical false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

variable (S : SimpleGraph V) [DecidableRel S.Adj]


noncomputable def gc16_splitSigmaEquiv (m : ↥S.edgeFinset → ℕ) :
    {pq : (↥S.edgeFinset → ℕ) × (↥S.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e} ≃
      Σ K₂ : {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ m e},
        {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ m e - K₂.1 e} where
  toFun K := ⟨⟨K.1.2, fun e => by have := K.2 e; omega⟩,
    ⟨K.1.1, fun e => by show K.1.1 e ≤ m e - K.1.2 e; have := K.2 e; omega⟩⟩
  invFun s := ⟨(s.2.1, s.1.1), fun e => by
    show s.2.1 e + s.1.1 e ≤ m e
    have h2 : s.2.1 e ≤ m e - s.1.1 e := s.2.2 e
    have h1 := s.1.2 e; omega⟩
  left_inv K := by ext <;> simp
  right_inv s := by rcases s with ⟨⟨K₂, hK₂⟩, ⟨K₁, hK₁⟩⟩; rfl


end StatMech.Walls
