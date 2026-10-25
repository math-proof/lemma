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
import Theorem.StatisticalMechanics.Code.Walls.gc16core
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


noncomputable def gc16_edgeNativeEquiv (p : ↥S.edgeFinset → ℕ) :
    {K : ↥S.edgeFinset → ℕ // ∀ e, K e ≤ p e} ≃
      {K : Sharpness.Current V // ∀ e, K e ≤ ofEdgeFun S p e} where
  toFun K := ⟨ofEdgeFun S K.1, fun e => by
    simp only [ofEdgeFun]; by_cases he : e ∈ S.edgeFinset <;> simp [he, K.2]⟩
  invFun K := ⟨fun e => K.1 e.1, fun e => by
    have hk := K.2 e.1; simp only [ofEdgeFun, e.2, dif_pos] at hk; exact hk⟩
  left_inv K := by
    apply Subtype.ext; funext e
    simp only [ofEdgeFun, e.2, dif_pos]
  right_inv K := by
    apply Subtype.ext; funext e
    by_cases he : e ∈ S.edgeFinset
    · simp only [ofEdgeFun, he, dif_pos]
    · have hk := K.2 e; simp only [ofEdgeFun, he, dif_neg, not_false_iff] at hk ⊢
      omega


end StatMech.Walls
