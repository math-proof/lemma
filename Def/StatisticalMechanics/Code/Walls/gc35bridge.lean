/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc35bridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc34resummation
import Theorem.StatisticalMechanics.Code.Walls.gc33witness.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.ClaimIsingFull.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.style.show false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def gc35_splitEquiv (m₀ : ↥G.edgeFinset → ℕ) :
    {K : Sharpness.Current V // ∀ e, K e ≤ (Sharpness.ofEdgeFun G m₀) e}
      ≃ {p : ↥G.edgeFinset → ℕ // p ≤ m₀} where
  toFun K := ⟨fun i => K.1 i.1, fun i => by
    have := K.2 i.1
    unfold Sharpness.ofEdgeFun at this
    rw [dif_pos i.2] at this
    exact this⟩
  invFun p := ⟨Sharpness.ofEdgeFun G p.1, fun e => by
    unfold Sharpness.ofEdgeFun
    by_cases h : e ∈ G.edgeFinset
    · rw [dif_pos h, dif_pos h]; exact p.2 _
    · rw [dif_neg h, dif_neg h]⟩
  left_inv K := by
    apply Subtype.ext
    funext e
    show (Sharpness.ofEdgeFun G (fun i => K.1 i.1)) e = K.1 e
    unfold Sharpness.ofEdgeFun
    by_cases h : e ∈ G.edgeFinset
    · rw [dif_pos h]
    · rw [dif_neg h]
      have := K.2 e
      unfold Sharpness.ofEdgeFun at this
      rw [dif_neg h] at this
      omega
  right_inv p := by
    apply Subtype.ext
    funext i
    show (Sharpness.ofEdgeFun G p.1) i.1 = p.1 i
    unfold Sharpness.ofEdgeFun
    rw [dif_pos i.2]


end StatMech.Walls
