/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ComponentThirdSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCombinatorics
import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part7
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in

theorem finiteBoundaryGhostDecrementedSourceWeightVertexSigma_sourceSplit
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    (∑ a ∈
        finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport
          n Ω v,
        finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
          β H n v a) =
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
        β H n Ω v +
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceInactiveRemainder
        β H n Ω v := by
  unfold finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceInactiveRemainder
  exact
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSubcase_filter_add_filter_not
      β H
      (finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport
        n Ω v)
      (fun a => finiteBoundaryGhostFullSourceOnePoint n a.1)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_eq_sourceSplit
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n Ω v =
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
        β H n Ω v +
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceInactiveRemainder
        β H n Ω v := by
  calc
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n Ω v =
        ∑ a ∈
          finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport
            n Ω v,
          finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
            β H n v a :=
      (finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport_sum_eq_vertexCutoffSum
        β H n Ω v).symm
    _ =
        finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
            β H n Ω v +
          finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceInactiveRemainder
            β H n Ω v :=
      finiteBoundaryGhostDecrementedSourceWeightVertexSigma_sourceSplit
        β H n Ω v

set_option linter.style.longLine false in


theorem
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution_eq_vertexCutoffSum_filter_fullSourceOnePoint
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
        β H n Ω v =
      finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n
        (Ω.filter (fun m => finiteBoundaryGhostFullSourceOnePoint n m)) v := by
  classical
  let S :=
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport
      n Ω v
  let P :
      Sigma (fun m :
        ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ =>
        finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v) → Prop :=
    fun a => finiteBoundaryGhostFullSourceOnePoint n a.1
  have hfilter :
      S.filter P =
        finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport
          n (Ω.filter (fun m => finiteBoundaryGhostFullSourceOnePoint n m)) v := by
    ext a
    simp [S, P, finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport_mem]
  unfold finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
  rw [hfilter]
  rw [finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport_sum_eq_vertexCutoffSum]

set_option linter.style.longLine false in


theorem
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution_eq_collapsedVertexCutoffDecrementIndex_image_sum
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
        β H n Ω v =
      ∑ d ∈
        (finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).image,
        (((finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ω v).fiber
            d).card : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d := by
  rw [
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution_eq_vertexCutoffSum_filter_fullSourceOnePoint,
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_filter_fullSourceOnePoint_eq_collapsedVertexCutoffDecrementIndex_image_sum]

set_option linter.style.longLine false in


theorem
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceInactiveRemainder_eq_vertexCutoffSum_filter_not_fullSourceOnePoint
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceInactiveRemainder
        β H n Ω v =
      finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n
        (Ω.filter (fun m => ¬ finiteBoundaryGhostFullSourceOnePoint n m)) v := by
  classical
  let S :=
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport
      n Ω v
  let P :
      Sigma (fun m :
        ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ =>
        finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v) → Prop :=
    fun a => ¬ finiteBoundaryGhostFullSourceOnePoint n a.1
  have hfilter :
      S.filter P =
        finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport
          n (Ω.filter (fun m => ¬ finiteBoundaryGhostFullSourceOnePoint n m)) v := by
    ext a
    simp [S, P, finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport_mem]
  unfold finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceInactiveRemainder
  rw [hfilter]
  rw [finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport_sum_eq_vertexCutoffSum]

set_option linter.style.longLine false in


theorem
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceInactiveRemainder_eq_fullSourceClassifiedVertexCurrentSupportDecrementIndex_image_sum
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceInactiveRemainder
        β H n Ω v =
      ∑ D ∈
          (finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex
            (Ω.filter
              (fun m => ¬ finiteBoundaryGhostFullSourceOnePoint n m)) v).image,
        (((finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex
            (Ω.filter
              (fun m => ¬ finiteBoundaryGhostFullSourceOnePoint n m)) v).fiber
              D).card : ℝ) *
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceDataWeight
            β H D := by
  rw [
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceInactiveRemainder_eq_vertexCutoffSum_filter_not_fullSourceOnePoint,
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_eq_fullSourceClassifiedVertexCurrentSupportDecrementIndex_image_sum]

set_option linter.style.longLine false in


theorem
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceInactiveRemainder_le_fullSourceClassifiedVertexCurrentSupportDecrementedBoundaryGhostMultiplicity_succ_weight_sum
    {β H : ℝ} (n : ℕ)
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceInactiveRemainder
        β H n Ω v ≤
      ∑ D ∈
        (finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex
          (Ω.filter
            (fun m => ¬ finiteBoundaryGhostFullSourceOnePoint n m)) v).image,
        (((D.2.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 : ℕ) :
          ℝ) *
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceDataWeight
            β H D) := by
  rw [
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceInactiveRemainder_eq_vertexCutoffSum_filter_not_fullSourceOnePoint]
  exact
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_le_fullSourceClassifiedVertexCurrentSupportDecrementedBoundaryGhostMultiplicity_succ_weight_sum
      hβ hH
      (Ω.filter (fun m => ¬ finiteBoundaryGhostFullSourceOnePoint n m)) v

end Exact3D
end StatMech
