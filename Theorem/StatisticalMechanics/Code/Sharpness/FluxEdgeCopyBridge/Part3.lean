/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FluxEdgeCopyBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.Switching.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Def.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
open Finset BigOperators
open scoped symmDiff Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Sharpness

namespace FluxEdgeCopy

variable {E : Type*} [Fintype E] [DecidableEq E] {β : E → Type*}
  [∀ e, Fintype (β e)] [∀ e, DecidableEq (β e)]


open StatMech.Sharpness (ofEdgeFun)

open StatMech.Sharpness.RandomCurrent (degK adjStep connK)

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem sourcePairSum_conv_factor (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V)
    (W : (↥G.edgeFinset → ℕ) → ℝ) (hWb : ∀ m, |W m| ≤ 1) :
    (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
        ((if sources G (ofEdgeFun G pq.1) = A then weight G β J (ofEdgeFun G pq.1) else 0)
            * (if sources G (ofEdgeFun G pq.2) = B then weight G β J (ofEdgeFun G pq.2) else 0))
          * W (fun e => pq.1 e + pq.2 e))
      = ∑' m : ↥G.edgeFinset → ℕ,
          (∑ K : {p : ↥G.edgeFinset → ℕ // p ≤ m},
            ((if sources G (ofEdgeFun G K.1) = A then weight G β J (ofEdgeFun G K.1) else 0)
              * (if sources G (ofEdgeFun G (fun e => m e - K.1 e)) = B
                    then weight G β J (ofEdgeFun G (fun e => m e - K.1 e)) else 0)))
            * W m := by
  set f : (↥G.edgeFinset → ℕ) → ℝ :=
    fun p => if sources G (ofEdgeFun G p) = A then weight G β J (ofEdgeFun G p) else 0 with hf
  set g : (↥G.edgeFinset → ℕ) → ℝ :=
    fun q => if sources G (ofEdgeFun G q) = B then weight G β J (ofEdgeFun G q) else 0 with hg
  have hfg_norm : Summable
      (fun z : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) => ‖f z.1 * g z.2‖) := by
    apply ((summable_norm_currentSum_summand G β J A).mul_of_nonneg
      (summable_norm_currentSum_summand G β J B)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).congr
    intro z; rw [norm_mul]
  have hsummand : Summable (fun z : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) =>
      (f z.1 * g z.2) * W (fun e => z.1 e + z.2 e)) := by
    apply Summable.of_norm
    apply hfg_norm.of_nonneg_of_le (fun _ => norm_nonneg _) (fun z => ?_)
    rw [norm_mul]
    calc ‖f z.1 * g z.2‖ * ‖W (fun e => z.1 e + z.2 e)‖
        ≤ ‖f z.1 * g z.2‖ * 1 := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          rw [Real.norm_eq_abs]; exact hWb _
      _ = ‖f z.1 * g z.2‖ := mul_one _
  set F : (Σ m : (↥G.edgeFinset → ℕ), {p : ↥G.edgeFinset → ℕ // p ≤ m}) → ℝ :=
    fun s => (f s.2.1 * g (fun e => s.1 e - s.2.1 e)) * W s.1 with hF
  have hcomp : ∀ z : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
      (f z.1 * g z.2) * W (fun e => z.1 e + z.2 e) = F (pairEquivSigma z) := by
    rintro ⟨p, q⟩
    simp only [hF, pairEquivSigma, Equiv.coe_fn_mk]
    have hsub : (fun e => (p e + q e) - p e) = q := by ext e; simp
    rw [hsub]
  have hsumF : Summable F := by
    rw [← (pairEquivSigma (E := ↥G.edgeFinset)).summable_iff]
    exact hsummand.congr (fun z => hcomp z)
  rw [tsum_congr hcomp, (pairEquivSigma (E := ↥G.edgeFinset)).tsum_eq F,
    Summable.tsum_sigma hsumF]
  refine tsum_congr (fun m => ?_)
  rw [tsum_fintype, Finset.sum_mul]


theorem sourcePairDisconnSum_eq_edgecopy (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V) (u v : V) :
    sourcePairDisconnSum G β J A B u v
      = ∑' m : ↥G.edgeFinset → ℕ,
          (∑ S : Finset (Copy G m),
            (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0)
              * (if RandomCurrent.sources (endsM G m) (univ \ S) = B then 1 else 0)
              * (if ¬ RandomCurrent.connK (endsM G m) univ u v then 1 else 0))
          * weight G β J (ofEdgeFun G m) := by
  unfold sourcePairDisconnSum
  rw [sourcePairSum_conv_factor G β J A B
    (fun m => if ¬ CurrentConnected G (ofEdgeFun G m) u v then 1 else 0)
    (fun m => by by_cases h : CurrentConnected G (ofEdgeFun G m) u v <;> simp [h])]
  refine tsum_congr (fun m => ?_)
  rw [Finset.sum_mul]
  exact sourcePair_superposition_bridge_disconn G β J A B m u v

end FluxEdgeCopy
end Sharpness
end StatMech
