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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part17
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem finiteCurrentTwoPointRatio_eq_expectationJ
    (d n : ℕ) (β : ℝ) (x y : FK.boxVerts d n) :
    finiteCurrentTwoPointRatio d n β x y =
      Sharpness.expectationJ (FK.boxGraph d n) β (fun _ => 1)
        (finiteTwoPointSource d n x y) := by
  classical
  unfold finiteCurrentTwoPointRatio finiteTwoPointSource
  exact (Sharpness.current_representation
    (FK.boxGraph d n) β (fun _ => 1)
    (({x} : Finset (FK.boxVerts d n)) ∆ {y})).symm


theorem expectationJ_empty_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) :
    Sharpness.expectationJ G β J (∅ : Finset V) = 1 := by
  classical
  have hZ : Sharpness.partitionJ G β J ≠ 0 :=
    ne_of_gt (Sharpness.partitionJ_pos G β J)
  have hnum :
      (∑ s : ConfigSpace V,
        Ising.spinProd (∅ : Finset V) s * Sharpness.boltzmannJ G β J s)
        = Sharpness.partitionJ G β J := by
    simp [Sharpness.partitionJ]
  unfold Sharpness.expectationJ
  rw [hnum]
  exact div_self hZ


theorem currentSum_empty_pos
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) :
    0 < Sharpness.currentSum G β J (∅ : Finset V) := by
  have hpart :
      Sharpness.partitionJ G β J =
        (2 : ℝ) ^ Fintype.card V *
          Sharpness.currentSum G β J (∅ : Finset V) :=
    Sharpness.partitionJ_eq_currentSum G β J
  have hprod :
      0 < (2 : ℝ) ^ Fintype.card V *
          Sharpness.currentSum G β J (∅ : Finset V) := by
    simpa [hpart] using Sharpness.partitionJ_pos G β J
  have htwo : 0 < (2 : ℝ) ^ Fintype.card V := by positivity
  nlinarith [hprod, htwo]


theorem currentSum_empty_ne_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) :
    Sharpness.currentSum G β J (∅ : Finset V) ≠ 0 :=
  ne_of_gt (currentSum_empty_pos G β J)


theorem currentSum_pos_of_positive_edgeCurrent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (m : ↥G.edgeFinset → ℕ)
    (hsrc : Sharpness.sources G (Sharpness.ofEdgeFun G m) = A)
    (hweight :
      0 < Sharpness.weight G β J (Sharpness.ofEdgeFun G m)) :
    0 < Sharpness.currentSum G β J A := by
  classical
  let f : (↥G.edgeFinset → ℕ) → ℝ :=
    fun m' =>
      if Sharpness.sources G (Sharpness.ofEdgeFun G m') = A then
        Sharpness.weight G β J (Sharpness.ofEdgeFun G m')
      else
        0
  have hsum : Summable f := by
    simpa [f] using
      (Sharpness.summable_norm_currentSum_summand G β J A).of_norm
  have hnonneg : ∀ m', 0 ≤ f m' := by
    intro m'
    dsimp [f]
    by_cases hsrc' : Sharpness.sources G (Sharpness.ofEdgeFun G m') = A
    · rw [if_pos hsrc']
      exact Sharpness.ssl_weight_nonneg G β J hβ hJ
        (Sharpness.ofEdgeFun G m')
    · rw [if_neg hsrc']
  have hmpos : 0 < f m := by
    dsimp [f]
    rw [if_pos hsrc]
    exact hweight
  simpa [Sharpness.currentSum, f] using
    Summable.tsum_pos hsum hnonneg m hmpos


theorem expectationJ_pos_of_positive_edgeCurrent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (m : ↥G.edgeFinset → ℕ)
    (hsrc : Sharpness.sources G (Sharpness.ofEdgeFun G m) = A)
    (hweight :
      0 < Sharpness.weight G β J (Sharpness.ofEdgeFun G m)) :
    0 < Sharpness.expectationJ G β J A := by
  rw [Sharpness.current_representation]
  exact
    div_pos
      (currentSum_pos_of_positive_edgeCurrent G β J A hβ hJ m
        hsrc hweight)
      (currentSum_empty_pos G β J)

set_option linter.style.longLine false in


theorem currentSum_pos_of_expectationJ_pos
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V)
    (hpos : 0 < Sharpness.expectationJ G β J A) :
    0 < Sharpness.currentSum G β J A := by
  rw [Sharpness.current_representation] at hpos
  have hZ : 0 < Sharpness.currentSum G β J (∅ : Finset V) :=
    currentSum_empty_pos G β J
  have hmul :
      0 < (Sharpness.currentSum G β J A /
          Sharpness.currentSum G β J (∅ : Finset V)) *
        Sharpness.currentSum G β J (∅ : Finset V) :=
    mul_pos hpos hZ
  simpa [ne_of_gt hZ] using hmul

set_option linter.style.longLine false in


theorem sourcePairSum_empty_pos_of_expectationJ_pos
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V)
    (hpos : 0 < Sharpness.expectationJ G β J A) :
    0 < Sharpness.sourcePairSum G β J A (∅ : Finset V) := by
  rw [Sharpness.sourcePairSum_eq_mul]
  exact mul_pos
    (currentSum_pos_of_expectationJ_pos G β J A hpos)
    (currentSum_empty_pos G β J)

set_option linter.style.longLine false in


theorem sourcePairSum_pos_of_expectationJ_pos
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V)
    (hA : 0 < Sharpness.expectationJ G β J A)
    (hB : 0 < Sharpness.expectationJ G β J B) :
    0 < Sharpness.sourcePairSum G β J A B := by
  rw [Sharpness.sourcePairSum_eq_mul]
  exact mul_pos
    (currentSum_pos_of_expectationJ_pos G β J A hA)
    (currentSum_pos_of_expectationJ_pos G β J B hB)


theorem currentSum_ratio_le_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) (r : ℝ) :
    Sharpness.currentSum G β J A /
        Sharpness.currentSum G β J (∅ : Finset V) ≤ r ↔
      Sharpness.currentSum G β J A ≤
        r * Sharpness.currentSum G β J (∅ : Finset V) := by
  rw [div_le_iff₀ (currentSum_empty_pos G β J)]


theorem currentSum_eq_zero_of_expectationJ_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V)
    (hzero : Sharpness.expectationJ G β J A = 0) :
    Sharpness.currentSum G β J A = 0 := by
  rw [Sharpness.current_representation] at hzero
  have hden : Sharpness.currentSum G β J (∅ : Finset V) ≠ 0 :=
    currentSum_empty_ne_zero G β J
  have hmul :=
    congrArg (fun t : ℝ => t * Sharpness.currentSum G β J (∅ : Finset V))
      hzero
  simpa [hden] using hmul


theorem sourcePairSum_empty_eq_zero_of_expectationJ_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V)
    (hzero : Sharpness.expectationJ G β J A = 0) :
    Sharpness.sourcePairSum G β J A (∅ : Finset V) = 0 := by
  rw [Sharpness.sourcePairSum_eq_mul]
  rw [currentSum_eq_zero_of_expectationJ_eq_zero G β J A hzero]
  simp


theorem currentSum_bound_of_sourcePairSum_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) (r : ℝ)
    (hpair :
      Sharpness.sourcePairSum G β J A (∅ : Finset V) ≤
        r * Sharpness.sourcePairSum G β J (∅ : Finset V)
          (∅ : Finset V)) :
    Sharpness.currentSum G β J A ≤
      r * Sharpness.currentSum G β J (∅ : Finset V) := by
  rw [Sharpness.sourcePairSum_eq_mul] at hpair
  rw [Sharpness.sourcePairSum_eq_mul] at hpair
  have hZpos : 0 < Sharpness.currentSum G β J (∅ : Finset V) :=
    currentSum_empty_pos G β J
  nlinarith [hpair, hZpos]


theorem expectationJ_le_of_sourcePairSum_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) (r : ℝ)
    (hpair :
      Sharpness.sourcePairSum G β J A (∅ : Finset V) ≤
        r * Sharpness.sourcePairSum G β J (∅ : Finset V)
          (∅ : Finset V)) :
    Sharpness.expectationJ G β J A ≤ r := by
  rw [Sharpness.current_representation]
  exact
    (currentSum_ratio_le_iff G β J A r).2
      (currentSum_bound_of_sourcePairSum_bound G β J A r hpair)


end Exact3D
end StatMech
