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
import Def.StatisticalMechanics.Code.Walls.gc16core
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


theorem gc16_tpsum_symm (β : ℝ) (J : Sym2 V → ℝ) (m : ↥S.edgeFinset → ℕ) (A B : Finset V) :
    gc15_tpsum S β J m A B = gc15_tpsum S β J m B A := by
  unfold gc15_tpsum
  rw [← Equiv.sum_comp (gc16_swapSplit S m)]
  refine Finset.sum_congr rfl (fun K _ => ?_)
  simp only [gc16_swapSplit, Equiv.coe_fn_mk]
  have hsub : (fun e => m e - K.1.2 e - K.1.1 e) = (fun e => m e - K.1.1 e - K.1.2 e) := by
    ext e; omega
  rw [hsub]; ring


theorem gc16_tpsum_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (m : ↥S.edgeFinset → ℕ) (A B : Finset V) :
    0 ≤ gc15_tpsum S β J m A B := by
  unfold gc15_tpsum
  refine Finset.sum_nonneg (fun K _ => ?_)
  have hw : ∀ (n : ↥S.edgeFinset → ℕ), (0:ℝ) ≤ weight S β J (ofEdgeFun S n) :=
    fun n => asd_weight_nonneg S β J hβ hJ _
  have h1 : (0:ℝ) ≤ (if sources S (ofEdgeFun S K.1.1) = A then weight S β J (ofEdgeFun S K.1.1) else 0) := by
    split <;> [exact hw _; rfl]
  have h2 : (0:ℝ) ≤ (if sources S (ofEdgeFun S K.1.2) = B then weight S β J (ofEdgeFun S K.1.2) else 0) := by
    split <;> [exact hw _; rfl]
  exact mul_nonneg (mul_nonneg h1 h2) (hw _)


theorem gc16_tFiber_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (A B C : Finset V) (m : ↥S.edgeFinset → ℕ) :
    0 ≤ gc15_tFiber S β J A B C m := by
  unfold gc15_tFiber
  split
  · exact gc16_tpsum_nonneg S β J hβ hJ m A B
  · rfl


end StatMech.Walls
