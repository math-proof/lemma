/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Claim1IsingComplete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.Claim1IsingFull.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.ClaimIsingFull.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.Simon.Part3
import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
import Def.StatisticalMechanics.Code.Sharpness.Claim1IsingComplete.Part2
open SimpleGraph Finset
open scoped BigOperators symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000


namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


open FluxEdgeCopy


namespace FluxEdgeCopy

theorem sources_univ_eq_symmDiff (m : ↥G.edgeFinset → ℕ) (K : Finset (Copy G m)) :
    RandomCurrent.sources (endsM G m) (univ : Finset (Copy G m)) =
      RandomCurrent.sources (endsM G m) K ∆
        RandomCurrent.sources (endsM G m) ((univ : Finset (Copy G m)) \ K) := by
  rw [← RandomCurrent.sources_symmDiff]
  congr 1
  ext i
  simp


theorem edgecopy_sourcePair_switching (m : ↥G.edgeFinset → ℕ) (A : Finset V)
    {u v : V} (huv : u ≠ v) :
    (∑ K : Finset (Copy G m),
        (if RandomCurrent.sources (endsM G m) K = A ∆ {u, v} then (1 : ℝ) else 0) *
          (if RandomCurrent.sources (endsM G m) ((univ : Finset (Copy G m)) \ K) = {u, v}
            then 1 else 0))
      = ∑ K : Finset (Copy G m),
          (if RandomCurrent.sources (endsM G m) K = A then (1 : ℝ) else 0) *
            (if RandomCurrent.sources (endsM G m) ((univ : Finset (Copy G m)) \ K) = ∅
              then 1 else 0) *
            (if RandomCurrent.connK (endsM G m) univ u v then 1 else 0) := by
  let U : Finset (Copy G m) := univ
  by_cases hU : RandomCurrent.sources (endsM G m) U = A
  · have hleft : ∀ K : Finset (Copy G m),
        RandomCurrent.sources (endsM G m) K = A ∆ {u, v} →
          RandomCurrent.sources (endsM G m) (U \ K) = {u, v} := by
      intro K hK
      have hs := sources_univ_eq_symmDiff G m K
      rw [show (univ : Finset (Copy G m)) = U from rfl, hU, hK] at hs
      ext z
      have hz := Finset.ext_iff.mp hs z
      simp only [Finset.mem_symmDiff] at hz ⊢
      tauto
    have hright : ∀ K : Finset (Copy G m),
        RandomCurrent.sources (endsM G m) K = A →
          RandomCurrent.sources (endsM G m) (U \ K) = ∅ := by
      intro K hK
      have hs := sources_univ_eq_symmDiff G m K
      rw [show (univ : Finset (Copy G m)) = U from rfl, hU, hK] at hs
      ext z
      have hz := Finset.ext_iff.mp hs z
      simp only [Finset.mem_symmDiff, Finset.notMem_empty] at hz ⊢
      tauto
    have hsw := RandomCurrent.switching_lemma (endsM G m) U
      (fun i _ => endsM_not_isDiag G m i) A hU huv (fun _ => (1 : ℝ))
    have hL : (∑ K : Finset (Copy G m),
          (if RandomCurrent.sources (endsM G m) K = A ∆ {u, v} then (1 : ℝ) else 0) *
            (if RandomCurrent.sources (endsM G m) (U \ K) = {u, v} then 1 else 0)) =
        ∑ _K ∈ U.powerset.filter
          (fun K => RandomCurrent.sources (endsM G m) K = A ∆ {u, v}), (1 : ℝ) := by
      rw [Finset.sum_filter]
      simp only [U, Finset.mem_powerset, Finset.subset_univ, if_true]
      apply Finset.sum_congr rfl
      intro K _
      by_cases hK : RandomCurrent.sources (endsM G m) K = A ∆ {u, v}
      · rw [if_pos hK, if_pos (by simpa [U] using hleft K hK)]
        norm_num
      · simp [hK]
    have hR : (∑ K : Finset (Copy G m),
          (if RandomCurrent.sources (endsM G m) K = A then (1 : ℝ) else 0) *
            (if RandomCurrent.sources (endsM G m) (U \ K) = ∅ then 1 else 0) *
            (if RandomCurrent.connK (endsM G m) U u v then 1 else 0)) =
        ∑ _K ∈ U.powerset.filter (fun K => RandomCurrent.sources (endsM G m) K = A),
          (1 : ℝ) * (if RandomCurrent.connK (endsM G m) U u v then 1 else 0) := by
      rw [Finset.sum_filter]
      simp only [U, Finset.mem_powerset, Finset.subset_univ, if_true]
      apply Finset.sum_congr rfl
      intro K _
      by_cases hK : RandomCurrent.sources (endsM G m) K = A
      · rw [if_pos hK, if_pos (by simpa [U] using hright K hK), one_mul]
        simp [hK]
      · simp [hK]
    rw [show (univ : Finset (Copy G m)) = U from rfl, hL, hR]
    exact hsw
  · have hzero : ∀ K : Finset (Copy G m),
        ¬ (RandomCurrent.sources (endsM G m) K = A ∆ {u, v} ∧
          RandomCurrent.sources (endsM G m) (U \ K) = {u, v}) := by
      rintro K ⟨hK, hC⟩
      apply hU
      have hs := sources_univ_eq_symmDiff G m K
      rw [show (univ : Finset (Copy G m)) = U from rfl, hK, hC] at hs
      ext z
      have hz := Finset.ext_iff.mp hs z
      simp only [Finset.mem_symmDiff] at hz ⊢
      tauto
    have hzero' : ∀ K : Finset (Copy G m),
        ¬ (RandomCurrent.sources (endsM G m) K = A ∧
          RandomCurrent.sources (endsM G m) (U \ K) = ∅) := by
      rintro K ⟨hK, hC⟩
      apply hU
      have hs := sources_univ_eq_symmDiff G m K
      rw [show (univ : Finset (Copy G m)) = U from rfl, hK, hC] at hs
      calc
        RandomCurrent.sources (endsM G m) U = A ∆ (∅ : Finset V) := hs
        _ = A := by ext z; simp [Finset.mem_symmDiff]
    have hLzero : (∑ K : Finset (Copy G m),
        (if RandomCurrent.sources (endsM G m) K = A ∆ {u, v} then (1 : ℝ) else 0) *
          (if RandomCurrent.sources (endsM G m) (U \ K) = {u, v} then 1 else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro K _
      by_cases hK : RandomCurrent.sources (endsM G m) K = A ∆ {u, v}
      · have hC : RandomCurrent.sources (endsM G m) (U \ K) ≠ {u, v} :=
          fun h => hzero K ⟨hK, h⟩
        simp [hK, hC]
      · simp [hK]
    have hRzero : (∑ K : Finset (Copy G m),
        (if RandomCurrent.sources (endsM G m) K = A then (1 : ℝ) else 0) *
          (if RandomCurrent.sources (endsM G m) (U \ K) = ∅ then 1 else 0) *
          (if RandomCurrent.connK (endsM G m) U u v then 1 else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro K _
      by_cases hK : RandomCurrent.sources (endsM G m) K = A
      · have hC : RandomCurrent.sources (endsM G m) (U \ K) ≠ ∅ :=
          fun h => hzero' K ⟨hK, h⟩
        simp [hK, hC]
      · simp [hK]
    change (∑ K : Finset (Copy G m),
        (if RandomCurrent.sources (endsM G m) K = A ∆ {u, v} then (1 : ℝ) else 0) *
          (if RandomCurrent.sources (endsM G m) (U \ K) = {u, v} then 1 else 0)) =
      ∑ K : Finset (Copy G m),
        (if RandomCurrent.sources (endsM G m) K = A then (1 : ℝ) else 0) *
          (if RandomCurrent.sources (endsM G m) (U \ K) = ∅ then 1 else 0) *
          (if RandomCurrent.connK (endsM G m) U u v then 1 else 0)
    rw [hLzero, hRzero]

end FluxEdgeCopy


theorem gatedSourcePairSum_switching (β : ℝ) (J : Sym2 V → ℝ)
    (A : Finset V) {u v : V} (huv : u ≠ v)
    (P : Current V → Prop) [DecidablePred P] :
    gatedSourcePairSum G β J (A ∆ {u, v}) {u, v} P =
      gatedSourcePairSum G β J A ∅
        (fun m => P m ∧ CurrentConnected G m u v) := by
  unfold gatedSourcePairSum
  rw [FluxEdgeCopy.sourcePairSum_conv_factor G β J (A ∆ {u, v}) {u, v}
      (fun m => if P (ofEdgeFun G m) then 1 else 0)
      (fun m => by by_cases h : P (ofEdgeFun G m) <;> simp [h])]
  rw [FluxEdgeCopy.sourcePairSum_conv_factor G β J A ∅
      (fun m => if P (ofEdgeFun G m) ∧ CurrentConnected G (ofEdgeFun G m) u v then 1 else 0)
      (fun m => by
        by_cases hP : P (ofEdgeFun G m) <;>
          by_cases hC : CurrentConnected G (ofEdgeFun G m) u v <;> simp [hP, hC])]
  refine tsum_congr (fun m => ?_)
  rw [FluxEdgeCopy.sourcePair_superposition_bridge G β J (A ∆ {u, v}) {u, v} m,
    FluxEdgeCopy.sourcePair_superposition_bridge G β J A ∅ m]
  rw [FluxEdgeCopy.edgecopy_sourcePair_switching G m A huv]
  have hconn := FluxEdgeCopy.connK_univ_iff G m u v
  by_cases hP : P (ofEdgeFun G m) <;>
    by_cases hC : CurrentConnected G (ofEdgeFun G m) u v <;>
    simp [hP, hC, hconn]


end Sharpness
end StatMech
