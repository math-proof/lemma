/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc37hdom.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc24deltabridge.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc28ghsrigid
import Theorem.StatisticalMechanics.Code.Walls.ghc_urselleqgap
import Theorem.StatisticalMechanics.Code.Walls.FaithfulnessAudit.Part2
import Theorem.StatisticalMechanics.Code.Ising.CurrentWeight.Part2
import Def.StatisticalMechanics.Code.Walls.gc37hdom.Part2
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.FieldGhostDict

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem gc37_sourcePairSum_conn_add_disconn (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V) (u v : V) :
    sourcePairSum G β J A B
      = gc37_sourcePairConnSum G β J A B u v
        + sourcePairDisconnSum G β J A B u v := by
  classical
  unfold sourcePairSum gc37_sourcePairConnSum sourcePairDisconnSum
  set f : (↥G.edgeFinset → ℕ) → ℝ :=
    fun p => if sources G (ofEdgeFun G p) = A then weight G β J (ofEdgeFun G p) else 0 with hf
  set g : (↥G.edgeFinset → ℕ) → ℝ :=
    fun q => if sources G (ofEdgeFun G q) = B then weight G β J (ofEdgeFun G q) else 0 with hg
  
  have hfg : Summable (fun z : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) => f z.1 * g z.2) :=
    summable_mul_of_summable_norm
      (summable_norm_currentSum_summand G β J A) (summable_norm_currentSum_summand G β J B)
  
  have hbound : ∀ (W : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) → ℝ),
      (∀ z, |W z| ≤ 1) →
      Summable (fun z : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) => (f z.1 * g z.2) * W z) := by
    intro W hW
    apply Summable.of_norm
    apply (hfg.norm).of_nonneg_of_le (fun _ => norm_nonneg _) (fun z => ?_)
    rw [norm_mul]
    calc ‖f z.1 * g z.2‖ * ‖W z‖ ≤ ‖f z.1 * g z.2‖ * 1 := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); rw [Real.norm_eq_abs]; exact hW z
      _ = ‖f z.1 * g z.2‖ := mul_one _
  have hconn := hbound
    (fun z => if CurrentConnected G (ofEdgeFun G (fun e => z.1 e + z.2 e)) u v then 1 else 0)
    (fun z => by
      by_cases h : CurrentConnected G (ofEdgeFun G (fun e => z.1 e + z.2 e)) u v <;> simp [h])
  have hdisc := hbound
    (fun z => if ¬ CurrentConnected G (ofEdgeFun G (fun e => z.1 e + z.2 e)) u v then 1 else 0)
    (fun z => by
      by_cases h : CurrentConnected G (ofEdgeFun G (fun e => z.1 e + z.2 e)) u v <;> simp [h])
  rw [← Summable.tsum_add hconn hdisc]
  refine tsum_congr (fun z => ?_)
  simp only [hf, hg]
  by_cases h : CurrentConnected G (ofEdgeFun G (fun e => z.1 e + z.2 e)) u v <;>
    simp only [h, not_true_eq_false, not_false_eq_true, if_true, if_false, mul_one, mul_zero,
      add_zero, zero_add]


theorem gc37_sourcePairConnSum_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (A B : Finset V) (u v : V) : 0 ≤ gc37_sourcePairConnSum G β J A B u v := by
  unfold gc37_sourcePairConnSum
  refine tsum_nonneg (fun z => ?_)
  refine mul_nonneg (mul_nonneg ?_ ?_) ?_
  · by_cases h : sources G (ofEdgeFun G z.1) = A
    · simp only [h, if_true]; exact acw_weight_nonneg G β J hβ hJ _
    · simp [h]
  · by_cases h : sources G (ofEdgeFun G z.2) = B
    · simp only [h, if_true]; exact acw_weight_nonneg G β J hβ hJ _
    · simp [h]
  · by_cases h : CurrentConnected G (ofEdgeFun G (fun e => z.1 e + z.2 e)) u v <;> simp [h]


end StatMech.Walls
