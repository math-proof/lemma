/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteIsingFKBridge.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.SurfaceTensionConvexity
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.SimonLiebFull.Part2
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part19
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem edgeCopySourcePairSummand_nonneg
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V)
    (m : ↥G.edgeFinset → ℕ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e) :
    0 ≤ edgeCopySourcePairSummand G β J A B m := by
  classical
  unfold edgeCopySourcePairSummand
  refine mul_nonneg ?_ ?_
  · refine Finset.sum_nonneg ?_
    intro S _hS
    by_cases hA :
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G m) S = A
    · rw [if_pos hA]
      by_cases hB :
          Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM G m)
            ((Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) \ S) = B
      · rw [if_pos hB]
        norm_num
      · rw [if_neg hB]
        norm_num
    · rw [if_neg hA]
      norm_num
  · rw [StatMech.Sharpness.weight_ofEdgeFun]
    exact Finset.prod_nonneg fun e _ =>
      div_nonneg (pow_nonneg (mul_nonneg hβ (hJ e.1)) _)
        (by positivity)

set_option linter.style.longLine false in


theorem weight_ofEdgeFun_mono_beta
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β γ : ℝ} (hβ : 0 ≤ β) (hβγ : β ≤ γ)
    (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (m : ↥G.edgeFinset → ℕ) :
    Sharpness.weight G β J (Sharpness.ofEdgeFun G m) ≤
      Sharpness.weight G γ J (Sharpness.ofEdgeFun G m) := by
  classical
  have hγ : 0 ≤ γ := hβ.trans hβγ
  rw [Sharpness.weight_ofEdgeFun, Sharpness.weight_ofEdgeFun]
  refine Finset.prod_le_prod ?_ ?_
  · intro e _he
    exact div_nonneg (pow_nonneg (mul_nonneg hβ (hJ e.1)) _)
      (by positivity)
  · intro e _he
    have hmul : β * J e.1 ≤ γ * J e.1 :=
      mul_le_mul_of_nonneg_right hβγ (hJ e.1)
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (mul_nonneg hβ (hJ e.1)) hmul (m e))
      (by positivity)

set_option linter.style.longLine false in


theorem edgeCopySourcePairSplitCount_nonneg
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ) (A B : Finset V) :
    0 ≤
      ∑ S : Finset (Sharpness.FluxEdgeCopy.Copy G m),
        (if Sharpness.RandomCurrent.sources
              (Sharpness.FluxEdgeCopy.endsM G m) S = A then
          (1 : ℝ)
        else
          0) *
        (if Sharpness.RandomCurrent.sources
              (Sharpness.FluxEdgeCopy.endsM G m)
              ((Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) \ S) = B then
          (1 : ℝ)
        else
          0) := by
  classical
  refine Finset.sum_nonneg ?_
  intro S _hS
  by_cases hA :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G m) S = A
  · rw [if_pos hA]
    by_cases hB :
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G m)
          ((Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) \ S) = B
    · rw [if_pos hB]
      norm_num
    · rw [if_neg hB]
      norm_num
  · rw [if_neg hA]
    norm_num

set_option linter.style.longLine false in


theorem edgeCopySourcePairSummand_mono_beta
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β γ : ℝ} (hβ : 0 ≤ β) (hβγ : β ≤ γ)
    (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (A B : Finset V) (m : ↥G.edgeFinset → ℕ) :
    edgeCopySourcePairSummand G β J A B m ≤
      edgeCopySourcePairSummand G γ J A B m := by
  classical
  unfold edgeCopySourcePairSummand
  exact mul_le_mul_of_nonneg_left
    (weight_ofEdgeFun_mono_beta G hβ hβγ J hJ m)
    (edgeCopySourcePairSplitCount_nonneg G m A B)


theorem edgeCopySourcePairDataWeight_le_summand
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) {A B : Finset V}
    (d : edgeCopySourcePairData G A B)
    (hweight : 0 ≤ edgeCopySourcePairDataWeight G β J d) :
    edgeCopySourcePairDataWeight G β J d ≤
      edgeCopySourcePairSummand G β J A B d.1 := by
  classical
  let F : Finset (Sharpness.FluxEdgeCopy.Copy G d.1) → ℝ :=
    fun S =>
      (if Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM G d.1) S = A then
        (1 : ℝ)
      else
        0) *
      (if Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM G d.1)
            ((Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G d.1)) \ S) = B then
        (1 : ℝ)
      else
        0)
  have hF_nonneg : ∀ S ∈ (Finset.univ : Finset
      (Finset (Sharpness.FluxEdgeCopy.Copy G d.1))), 0 ≤ F S := by
    intro S _hS
    dsimp [F]
    by_cases hA :
        Sharpness.RandomCurrent.sources
          (Sharpness.FluxEdgeCopy.endsM G d.1) S = A
    · rw [if_pos hA]
      by_cases hB :
          Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM G d.1)
            ((Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G d.1)) \ S) = B
      · rw [if_pos hB]
        norm_num
      · rw [if_neg hB]
        norm_num
    · rw [if_neg hA]
      norm_num
  have hdatum :
      F d.2.1 = 1 := by
    dsimp [F]
    rw [if_pos d.2.2.1, if_pos d.2.2.2]
    norm_num
  have hone_le :
      (1 : ℝ) ≤
        ∑ S : Finset (Sharpness.FluxEdgeCopy.Copy G d.1), F S := by
    simpa [hdatum] using
      (Finset.single_le_sum hF_nonneg
        (Finset.mem_univ d.2.1))
  have hweight_raw :
      0 ≤ Sharpness.weight G β J (Sharpness.ofEdgeFun G d.1) := by
    simpa [edgeCopySourcePairDataWeight] using hweight
  unfold edgeCopySourcePairDataWeight edgeCopySourcePairSummand
  change
    Sharpness.weight G β J (Sharpness.ofEdgeFun G d.1) ≤
      (∑ S : Finset (Sharpness.FluxEdgeCopy.Copy G d.1), F S) *
        Sharpness.weight G β J (Sharpness.ofEdgeFun G d.1)
  calc
    Sharpness.weight G β J (Sharpness.ofEdgeFun G d.1) =
        (1 : ℝ) * Sharpness.weight G β J (Sharpness.ofEdgeFun G d.1) := by
      ring
    _ ≤
        (∑ S : Finset (Sharpness.FluxEdgeCopy.Copy G d.1), F S) *
          Sharpness.weight G β J (Sharpness.ofEdgeFun G d.1) :=
      mul_le_mul_of_nonneg_right hone_le hweight_raw


theorem edgeCopySourcePairSummand_summable
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V) :
    Summable (fun m : ↥G.edgeFinset → ℕ =>
      edgeCopySourcePairSummand G β J A B m) := by
  classical
  simpa [edgeCopySourcePairSummand] using
    (Sharpness.GhostCurrentRep.gcr_summable_edgecopy G β J A B)


theorem edgeCopySourcePairSummand_le_edgeCopySourcePairSum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V)
    (m : ↥G.edgeFinset → ℕ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e) :
    edgeCopySourcePairSummand G β J A B m ≤
      edgeCopySourcePairSum G β J A B := by
  classical
  have hsummable :=
    edgeCopySourcePairSummand_summable G β J A B
  have hsingle :
      (∑ x ∈ ({m} : Finset (↥G.edgeFinset → ℕ)),
          edgeCopySourcePairSummand G β J A B x) ≤
        ∑' x : ↥G.edgeFinset → ℕ,
          edgeCopySourcePairSummand G β J A B x := by
    exact hsummable.sum_le_tsum {m} (fun x _hx =>
      edgeCopySourcePairSummand_nonneg G β J A B x hβ hJ)
  simpa [edgeCopySourcePairSum, edgeCopySourcePairSummand] using hsingle


theorem edgeCopySourcePairSum_nonneg
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e) :
    0 ≤ edgeCopySourcePairSum G β J A B := by
  classical
  unfold edgeCopySourcePairSum
  exact tsum_nonneg fun m => by
    simpa [edgeCopySourcePairSummand] using
      edgeCopySourcePairSummand_nonneg G β J A B m hβ hJ

set_option linter.style.longLine false in

theorem edgeCopySourcePairSum_mono_beta
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β γ : ℝ} (hβ : 0 ≤ β) (hβγ : β ≤ γ)
    (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (A B : Finset V) :
    edgeCopySourcePairSum G β J A B ≤ edgeCopySourcePairSum G γ J A B := by
  classical
  rw [edgeCopySourcePairSum, edgeCopySourcePairSum]
  exact
    (edgeCopySourcePairSummand_summable G β J A B).tsum_le_tsum
      (fun m => by
        simpa [edgeCopySourcePairSummand] using
          edgeCopySourcePairSummand_mono_beta G hβ hβγ J hJ A B m)
      (edgeCopySourcePairSummand_summable G γ J A B)


theorem sourcePairSum_eq_edgeCopySourcePairSum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V) :
    Sharpness.sourcePairSum G β J A B =
      edgeCopySourcePairSum G β J A B :=
  Sharpness.FluxEdgeCopy.sourcePairSum_eq_edgecopy G β J A B

set_option linter.style.longLine false in

theorem sourcePairSum_mono_beta
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {β γ : ℝ} (hβ : 0 ≤ β) (hβγ : β ≤ γ)
    (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (A B : Finset V) :
    Sharpness.sourcePairSum G β J A B ≤
      Sharpness.sourcePairSum G γ J A B := by
  rw [sourcePairSum_eq_edgeCopySourcePairSum,
    sourcePairSum_eq_edgeCopySourcePairSum]
  exact edgeCopySourcePairSum_mono_beta G hβ hβγ J hJ A B


theorem edgeCopySourcePairSum_eq_currentSum_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V) :
    edgeCopySourcePairSum G β J A B =
      Sharpness.currentSum G β J A * Sharpness.currentSum G β J B := by
  rw [← sourcePairSum_eq_edgeCopySourcePairSum G β J A B]
  rw [Sharpness.sourcePairSum_eq_mul]


theorem edgeCopySourcePairSum_empty_eq_collapsed
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) :
    edgeCopySourcePairSum G β J A (∅ : Finset V) =
      edgeCopySourcePairEmptyCollapsedSum G β J A := by
  unfold edgeCopySourcePairSum edgeCopySourcePairEmptyCollapsedSum
  refine tsum_congr (fun m => ?_)
  rw [Sharpness.GhostCurrentRep.gcr_pairCount_empty G m A]


theorem edgeCopySourcePairEmptyCollapsedSum_nonneg
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e) :
    0 ≤ edgeCopySourcePairEmptyCollapsedSum G β J A := by
  rw [← edgeCopySourcePairSum_empty_eq_collapsed G β J A]
  exact edgeCopySourcePairSum_nonneg G β J A (∅ : Finset V) hβ hJ


theorem edgeCopySourcePairEmptyCollapsedSum_eq_currentSum_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) :
    edgeCopySourcePairEmptyCollapsedSum G β J A =
      Sharpness.currentSum G β J A *
        Sharpness.currentSum G β J (∅ : Finset V) := by
  rw [← edgeCopySourcePairSum_empty_eq_collapsed G β J A]
  rw [← sourcePairSum_eq_edgeCopySourcePairSum G β J A (∅ : Finset V)]
  rw [Sharpness.sourcePairSum_eq_mul]


theorem edgeCopySourcePairEmptyCollapsedSum_empty_pos
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) :
    0 < edgeCopySourcePairEmptyCollapsedSum G β J (∅ : Finset V) := by
  rw [edgeCopySourcePairEmptyCollapsedSum_eq_currentSum_mul]
  exact mul_pos (currentSum_empty_pos G β J) (currentSum_empty_pos G β J)


theorem edgeCopySourcePairEmptyCollapsedSummand_summable
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) :
    Summable (fun m : ↥G.edgeFinset → ℕ =>
      ((if Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM G m)
            (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) = A then
          (1 : ℝ)
        else
          0) *
        (((Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)).powerset.filter
          (fun K =>
            Sharpness.RandomCurrent.sources
              (Sharpness.FluxEdgeCopy.endsM G m) K = A)).card : ℝ)) *
        Sharpness.weight G β J (Sharpness.ofEdgeFun G m)) := by
  classical
  have h :=
    Sharpness.GhostCurrentRep.gcr_summable_edgecopy
      G β J A (∅ : Finset V)
  exact h.congr (fun m => by
    rw [Sharpness.GhostCurrentRep.gcr_pairCount_empty G m A])


theorem sourcePairBound_of_edgeCopyBound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) (r : ℝ)
    (h :
      edgeCopySourcePairSum G β J A (∅ : Finset V) ≤
        r * edgeCopySourcePairSum G β J (∅ : Finset V)
          (∅ : Finset V)) :
    Sharpness.sourcePairSum G β J A (∅ : Finset V) ≤
      r * Sharpness.sourcePairSum G β J (∅ : Finset V)
        (∅ : Finset V) := by
  rw [sourcePairSum_eq_edgeCopySourcePairSum]
  rw [sourcePairSum_eq_edgeCopySourcePairSum]
  exact h


theorem edgeCopyBound_of_emptyCollapsedBound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) (r : ℝ)
    (h :
      edgeCopySourcePairEmptyCollapsedSum G β J A ≤
        r * edgeCopySourcePairEmptyCollapsedSum G β J (∅ : Finset V)) :
    edgeCopySourcePairSum G β J A (∅ : Finset V) ≤
      r * edgeCopySourcePairSum G β J (∅ : Finset V) (∅ : Finset V) := by
  simpa [edgeCopySourcePairSum_empty_eq_collapsed] using h


theorem edgeCopySourcePairSum_empty_eq_zero_of_expectationJ_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V)
    (hzero : Sharpness.expectationJ G β J A = 0) :
    edgeCopySourcePairSum G β J A (∅ : Finset V) = 0 := by
  rw [← sourcePairSum_eq_edgeCopySourcePairSum G β J A (∅ : Finset V)]
  exact sourcePairSum_empty_eq_zero_of_expectationJ_eq_zero G β J A hzero


theorem weight_ofEdgeFun_eq_zero_of_edge_coupling_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ)
    (m : ↥G.edgeFinset → ℕ) (e : ↥G.edgeFinset)
    (hm : 0 < m e) (hJ : J e.1 = 0) :
    Sharpness.weight G β J (Sharpness.ofEdgeFun G m) = 0 := by
  rw [StatMech.Sharpness.weight_ofEdgeFun]
  apply Finset.prod_eq_zero (Finset.mem_univ e)
  rw [hJ, mul_zero]
  rw [zero_pow (by omega), zero_div]


theorem weight_ofEdgeFun_nonneg_of_nonneg
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (m : ↥G.edgeFinset → ℕ) :
    0 ≤ Sharpness.weight G β J (Sharpness.ofEdgeFun G m) := by
  rw [StatMech.Sharpness.weight_ofEdgeFun]
  exact Finset.prod_nonneg fun e _ =>
    div_nonneg (pow_nonneg (mul_nonneg hβ (hJ e.1)) _)
      (by positivity)


theorem weight_ofEdgeFun_pos_of_pos_on_support
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ)
    (hβ : 0 < β)
    (m : ↥G.edgeFinset → ℕ)
    (hJ : ∀ e : ↥G.edgeFinset, 0 < m e → 0 < J e.1) :
    0 < Sharpness.weight G β J (Sharpness.ofEdgeFun G m) := by
  classical
  rw [StatMech.Sharpness.weight_ofEdgeFun]
  refine Finset.prod_pos ?_
  intro e _he
  by_cases hzero : m e = 0
  · simp [hzero]
  · have hmpos : 0 < m e := Nat.pos_of_ne_zero hzero
    exact
      div_pos
        (pow_pos (mul_pos hβ (hJ e hmpos)) _)
        (by positivity)


theorem weight_ofEdgeFun_decrement
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ)
    (m : ↥G.edgeFinset → ℕ) (e : ↥G.edgeFinset)
    (hm : 0 < m e) :
    ((m e : ℝ) * Sharpness.weight G β J (Sharpness.ofEdgeFun G m)) =
      (β * J e.1) *
        Sharpness.weight G β J
          (Sharpness.ofEdgeFun G (Function.update m e (m e - 1))) := by
  rw [StatMech.Sharpness.weight_ofEdgeFun]
  rw [StatMech.Sharpness.weight_ofEdgeFun]
  let term : ↥G.edgeFinset → ℝ :=
    fun x => (β * J x.1) ^ (m x) / (Nat.factorial (m x))
  let term' : ↥G.edgeFinset → ℝ :=
    fun x => (β * J x.1) ^ ((Function.update m e (m e - 1)) x) /
      (Nat.factorial ((Function.update m e (m e - 1)) x))
  change (m e : ℝ) * (∏ x, term x) = (β * J e.1) * ∏ x, term' x
  rw [Fintype.prod_eq_mul_prod_compl e term]
  rw [Fintype.prod_eq_mul_prod_compl e term']
  have hterm_e : (m e : ℝ) * term e = (β * J e.1) * term' e := by
    dsimp [term, term']
    rw [Function.update_self]
    obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
    rw [hr, Nat.factorial_succ, pow_succ]
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel_right, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    field_simp [Nat.factorial_ne_zero]
  have hrest :
      (∏ x ∈ ({e} : Finset ↥G.edgeFinset)ᶜ, term' x) =
        ∏ x ∈ ({e} : Finset ↥G.edgeFinset)ᶜ, term x := by
    refine Finset.prod_congr rfl ?_
    intro x hx
    have hne : x ≠ e := by
      intro hxe
      subst hxe
      simp at hx
    dsimp [term, term']
    rw [Function.update_of_ne hne]
  rw [hrest]
  calc
    (m e : ℝ) *
        (term e * ∏ i ∈ ({e} : Finset ↥G.edgeFinset)ᶜ, term i)
        = ((m e : ℝ) * term e) *
            ∏ i ∈ ({e} : Finset ↥G.edgeFinset)ᶜ, term i := by ring
    _ = ((β * J e.1) * term' e) *
            ∏ i ∈ ({e} : Finset ↥G.edgeFinset)ᶜ, term i := by rw [hterm_e]
    _ = (β * J e.1) *
          (term' e *
            ∏ i ∈ ({e} : Finset ↥G.edgeFinset)ᶜ, term i) := by ring


theorem randomCurrent_connK_firstExit_adjStep
    {ι V : Type*}
    (ends : ι → Sym2 V) (K : Finset ι) (S : Finset V) {o z : V}
    (hconn : Sharpness.RandomCurrent.connK ends K o z)
    (ho : o ∈ S) (hz : z ∉ S) :
    ∃ x y : V,
      x ∈ S ∧ y ∉ S ∧
        Sharpness.RandomCurrent.adjStep ends K x y ∧
        Sharpness.RandomCurrent.connK ends K o x := by
  classical
  revert ho hz
  induction hconn with
  | refl =>
      intro ho hz
      exact False.elim (hz ho)
  | @tail b c hpre hstep ih =>
      intro ho hz
      by_cases hb : b ∈ S
      · exact ⟨b, c, hb, hz, hstep, hpre⟩
      · exact ih ho hb


theorem randomCurrent_sources_singleton_of_ends_eq
    {ι V : Type*} [Fintype ι] [Fintype V] [DecidableEq V]
    (ends : ι → Sym2 V) {i : ι} {a b : V}
    (hi : ends i = s(a, b)) :
    Sharpness.RandomCurrent.sources ends ({i} : Finset ι) = {a, b} := by
  classical
  ext x
  rw [Sharpness.RandomCurrent.mem_sources]
  unfold Sharpness.RandomCurrent.degK
  rw [Finset.filter_singleton]
  rw [hi]
  by_cases hx : x ∈ (s(a, b) : Sym2 V)
  · rw [if_pos hx]
    simp only [Finset.card_singleton]
    rw [show Odd 1 ↔ True by simp]
    simp only [true_iff]
    simpa [Sym2.mem_iff] using hx
  · rw [if_neg hx]
    simp only [Finset.card_empty]
    rw [show Odd 0 ↔ False by simp]
    simp only [false_iff]
    simpa [Sym2.mem_iff] using hx


theorem randomCurrent_sources_sdiff_singleton
    {ι V : Type*} [DecidableEq ι] [Fintype ι] [Fintype V]
    [DecidableEq V]
    (ends : ι → Sym2 V) {K : Finset ι} {i : ι}
    (hiK : i ∈ K) :
    Sharpness.RandomCurrent.sources ends (K \ {i}) =
      Sharpness.RandomCurrent.sources ends K ∆
        Sharpness.RandomCurrent.sources ends ({i} : Finset ι) := by
  have hsdiff : K \ {i} = K ∆ ({i} : Finset ι) := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [hiK, Finset.mem_symmDiff]
    · simp [hji, Finset.mem_symmDiff]
  rw [hsdiff, Sharpness.RandomCurrent.sources_symmDiff]


theorem expectationJ_symmDiff_self_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (x : V) :
    Sharpness.expectationJ G β J (({x} : Finset V) ∆ {x}) = 1 := by
  simpa using expectationJ_empty_eq_one G β J


theorem sources_ofEdgeFun_path_count
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {a b : V} (p : G.Path a b) (hab : a ≠ b) :
    let m : ↥G.edgeFinset → ℕ := fun e => p.1.edges.count e.1
    Sharpness.sources G (Sharpness.ofEdgeFun G m) = ({a, b} : Finset V) := by
  classical
  dsimp
  ext x
  rw [Sharpness.mem_sources]
  have hsub : ∀ e ∈ p.1.edges, e ∈ G.edgeFinset := by
    intro e he
    exact SimpleGraph.mem_edgeFinset.mpr
      (SimpleGraph.Walk.edges_subset_edgeSet p.1 he)
  have hflux :
      Sharpness.incidentFlux G
          (Sharpness.ofEdgeFun G
            (fun e : ↥G.edgeFinset => p.1.edges.count e.1)) x =
        Sharpness.walkDeg p.1 x := by
    unfold Sharpness.incidentFlux Sharpness.ofEdgeFun
    calc
      ∑ e ∈ G.edgeFinset.filter (fun e => x ∈ e),
          (if h : e ∈ G.edgeFinset then
            p.1.edges.count ((⟨e, h⟩ : ↥G.edgeFinset).1) else 0) =
          ∑ e ∈ G.edgeFinset.filter (fun e => x ∈ e),
            p.1.edges.count e := by
        refine Finset.sum_congr rfl ?_
        intro e he
        have heG : e ∈ G.edgeFinset := (Finset.mem_filter.mp he).1
        rw [dif_pos heG]
      _ = Sharpness.walkDeg p.1 x :=
        Sharpness.sum_count_eq_walkDeg G p.1 x hsub
  rw [hflux]
  rw [Sharpness.walkDeg_odd_iff p.1 p.2 x]
  constructor
  · rintro ⟨hx, _⟩
    simpa [Finset.mem_insert, Finset.mem_singleton] using hx
  · intro hx
    exact ⟨by simpa [Finset.mem_insert, Finset.mem_singleton] using hx, hab⟩


theorem finiteCurrentTwoPointRatio_self_eq_one
    (d n : ℕ) (β : ℝ) (x : FK.boxVerts d n) :
    finiteCurrentTwoPointRatio d n β x x = 1 := by
  rw [finiteCurrentTwoPointRatio_eq_expectationJ]
  simpa [finiteTwoPointSource] using
    expectationJ_empty_eq_one (FK.boxGraph d n) β (fun _ => 1)


theorem simonLieb_singletonTarget_bound
    {V : Type*}
    {τ : V → V → ℝ} {o z : V} {S : Finset V} {w : V → V → ℝ}
    (hSL : Sharpness.SimonLieb τ o S w ({z} : Finset V))
    (hz : z ∉ S) (hzz : τ z z ≤ 1) :
    τ o z ≤ ∑ x ∈ S, w x z := by
  calc
    τ o z ≤ ∑ x ∈ S, ∑ y ∈ ({z} : Finset V), w x y * τ y z := by
      exact hSL.simon z hz
    _ = ∑ x ∈ S, w x z * τ z z := by
      simp
    _ ≤ ∑ x ∈ S, w x z := by
      exact Finset.sum_le_sum fun x _ =>
        mul_le_of_le_one_right (hSL.weight_nonneg x z) hzz


theorem simonLieb_singletonTarget_bound_expectationJ_symmDiff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ)
    {o z : V} {S : Finset V} {w : V → V → ℝ}
    (hSL : Sharpness.SimonLieb
      (fun a b => Sharpness.expectationJ G β J (({a} : Finset V) ∆ {b}))
      o S w ({z} : Finset V))
    (hz : z ∉ S) :
    Sharpness.expectationJ G β J (({o} : Finset V) ∆ {z})
      ≤ ∑ x ∈ S, w x z := by
  refine simonLieb_singletonTarget_bound hSL hz ?_
  simpa using le_of_eq (expectationJ_symmDiff_self_eq_one G β J z)


theorem finiteCurrentTwoPointRatio_nonneg
    (d n : ℕ) {β : ℝ} (hβ : 0 ≤ β) (x y : FK.boxVerts d n) :
    0 ≤ finiteCurrentTwoPointRatio d n β x y := by
  classical
  unfold finiteCurrentTwoPointRatio
  refine div_nonneg ?_ ?_
  · exact Sharpness.ssl_currentSum_nonneg (FK.boxGraph d n) β (fun _ => 1)
      hβ (fun _ => by norm_num) (finiteTwoPointSource d n x y)
  · exact Sharpness.ssl_currentSum_nonneg (FK.boxGraph d n) β (fun _ => 1)
      hβ (fun _ => by norm_num) ∅


end Exact3D
end StatMech
