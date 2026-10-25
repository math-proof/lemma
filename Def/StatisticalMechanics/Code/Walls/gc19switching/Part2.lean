/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc19switching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc16core.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7core
import Theorem.StatisticalMechanics.Code.Walls.gc6_munonneg
import Theorem.StatisticalMechanics.Code.Ising.HdomNativeWeight.Part3
import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
import Theorem.StatisticalMechanics.Code.Ising.TwoReplicaWeighted.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc19switching
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (S : SimpleGraph V) [DecidableRel S.Adj]


noncomputable def gc19_ref2 (m : ↥S.edgeFinset → ℕ) (P : Finset (Sym2 V))
    (K : {pq : (↥S.edgeFinset → ℕ) × (↥S.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e}) :
    {pq : (↥S.edgeFinset → ℕ) × (↥S.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e} :=
  ⟨(K.1.1, gc19_eref S (fun e => m e - K.1.1 e) P K.1.2), by
    intro e
    have hK := K.2 e
    have hbudget : ∀ e', K.1.2 e' ≤ (fun e => m e - K.1.1 e) e' := fun e' => by
      have := K.2 e'; simp only; omega
    have hle : gc19_eref S (fun e => m e - K.1.1 e) P K.1.2 e ≤ m e - K.1.1 e :=
      gc19_eref_le S (fun e => m e - K.1.1 e) P hbudget e
    simp only at hle ⊢
    omega⟩


noncomputable def gc19_ref2Equiv (m : ↥S.edgeFinset → ℕ) (P : Finset (Sym2 V)) :
    {pq : (↥S.edgeFinset → ℕ) × (↥S.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e} ≃
    {pq : (↥S.edgeFinset → ℕ) × (↥S.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e} where
  toFun := gc19_ref2 S m P
  invFun := gc19_ref2 S m P
  left_inv K := by
    apply Subtype.ext
    have hbudget : ∀ e, K.1.2 e ≤ m e - K.1.1 e := fun e => by have := K.2 e; omega
    have hinv := gc19_eref_involutive S (fun e => m e - K.1.1 e) P hbudget
    show ((K.1.1, gc19_eref S (fun e => m e - K.1.1 e) P
        (gc19_eref S (fun e => m e - K.1.1 e) P K.1.2)) : (_ × _)) = K.1
    rw [hinv]
  right_inv K := by
    apply Subtype.ext
    have hbudget : ∀ e, K.1.2 e ≤ m e - K.1.1 e := fun e => by have := K.2 e; omega
    have hinv := gc19_eref_involutive S (fun e => m e - K.1.1 e) P hbudget
    show ((K.1.1, gc19_eref S (fun e => m e - K.1.1 e) P
        (gc19_eref S (fun e => m e - K.1.1 e) P K.1.2)) : (_ × _)) = K.1
    rw [hinv]


end StatMech.Walls
