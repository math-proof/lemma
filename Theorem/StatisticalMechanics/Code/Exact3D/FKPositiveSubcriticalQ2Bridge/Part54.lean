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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part56
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport_sum_eq_fullSourceClassifiedVertexCurrentSupportDecrementIndex_domain_sum
    {β H : ℝ} {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    (∑ a ∈
        finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport
          n Ω v,
        finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
          β H n v a) =
      Finset.sum
        (finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex
          Ω v).domain
        (fun a =>
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceDataWeight
            β H
            ((finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex
              Ω v).map a)) := by
  classical
  unfold finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex
  refine Finset.sum_congr rfl ?_
  intro a _ha
  simpa [finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceDataWeight]
    using
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand_eq_fullSourceClassifiedDataWeight
        (β := β) (H := H) a

set_option linter.style.longLine false in


theorem
    finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex_domain_sum_eq_image_sum
    {β H : ℝ} {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    Finset.sum
        (finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex
          Ω v).domain
        (fun a =>
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceDataWeight
            β H
            ((finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex
              Ω v).map a)) =
      ∑ D ∈
          (finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex
            Ω v).image,
        (((finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex
            Ω v).fiber D).card : ℝ) *
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceDataWeight
            β H D :=
  FinsetFiberIndex.sum_fiber_weight
    (finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex
      Ω v)
    (finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceDataWeight β H)

set_option linter.style.longLine false in


theorem
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport_sum_eq_fullSourceClassifiedVertexCurrentSupportDecrementIndex_image_sum
    {β H : ℝ} {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    (∑ a ∈
        finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport
          n Ω v,
        finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
          β H n v a) =
      ∑ D ∈
          (finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex
            Ω v).image,
        (((finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex
            Ω v).fiber D).card : ℝ) *
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceDataWeight
            β H D := by
  rw [
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport_sum_eq_fullSourceClassifiedVertexCurrentSupportDecrementIndex_domain_sum,
    finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex_domain_sum_eq_image_sum]

set_option linter.style.longLine false in


theorem
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_eq_fullSourceClassifiedVertexCurrentSupportDecrementIndex_image_sum
    {β H : ℝ} {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n Ω v =
      ∑ D ∈
          (finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex
            Ω v).image,
        (((finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex
            Ω v).fiber D).card : ℝ) *
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceDataWeight
            β H D := by
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
        ∑ D ∈
          (finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex
            Ω v).image,
        (((finiteBoundaryGhostFullSourceClassifiedVertexCurrentSupportDecrementIndex
            Ω v).fiber D).card : ℝ) *
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceDataWeight
            β H D :=
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport_sum_eq_fullSourceClassifiedVertexCurrentSupportDecrementIndex_image_sum
        (β := β) (H := H) Ω v


theorem
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSubcase_sum_le_currentSupport_sum
    {β H : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset (Sigma (fun m :
      ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ =>
      finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v))) :
    (∑ a ∈ Ω,
        finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
          β H n v a) ≤
      ∑ a ∈
          finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport
            n (Ω.image Sigma.fst) v,
        finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
          β H n v a := by
  classical
  refine Finset.sum_le_sum_of_subset_of_nonneg ?hsub ?hnonneg
  · intro a ha
    rw [finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport_mem]
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  · intro a _ha _hnot
    exact
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand_nonneg
        (β := β) (H := H) hβ hH a


theorem
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSubcase_sum_le_vertexCutoffSum
    {β H : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset (Sigma (fun m :
      ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ =>
      finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v))) :
    (∑ a ∈ Ω,
        finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
          β H n v a) ≤
      finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum
        β H n (Ω.image Sigma.fst) v := by
  calc
    (∑ a ∈ Ω,
        finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
          β H n v a) ≤
      ∑ a ∈
          finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport
            n (Ω.image Sigma.fst) v,
        finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
          β H n v a :=
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSubcase_sum_le_currentSupport_sum
        (β := β) (H := H) hβ hH Ω
    _ =
      finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum
        β H n (Ω.image Sigma.fst) v :=
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport_sum_eq_vertexCutoffSum
        β H n (Ω.image Sigma.fst) v


theorem finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSubcase_mono
    {β H : ℝ} {n : ℕ} {v : FK.boxVerts 3 n}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    {Ω Ω' : Finset (Sigma (fun m :
      ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ =>
      finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v))}
    (hΩ : Ω ⊆ Ω') :
    (∑ a ∈ Ω,
        finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
          β H n v a) ≤
      ∑ a ∈ Ω',
        finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
          β H n v a := by
  classical
  exact
    Finset.sum_le_sum_of_subset_of_nonneg hΩ
      (fun a _ha _hnot =>
        finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand_nonneg
          (β := β) (H := H) hβ hH a)


theorem
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSubcase_filter_add_filter_not
    (β H : ℝ) {n : ℕ} {v : FK.boxVerts 3 n}
    (Ω : Finset (Sigma (fun m :
      ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ =>
      finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v)))
    (P : Sigma (fun m :
      ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ =>
      finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v) → Prop)
    [DecidablePred P] :
    (∑ a ∈ Ω,
        finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
          β H n v a) =
      (∑ a ∈ Ω.filter P,
        finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
          β H n v a) +
      ∑ a ∈ Ω.filter (fun a => ¬ P a),
        finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
          β H n v a := by
  exact
    (Finset.sum_filter_add_sum_filter_not Ω P
      (finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
        β H n v)).symm


theorem
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSubcase_sum_le_of_filter_le_filter_not_le
    (β H : ℝ) {n : ℕ} {v : FK.boxVerts 3 n}
    (Ω : Finset (Sigma (fun m :
      ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ =>
      finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v)))
    (P : Sigma (fun m :
      ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ =>
      finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v) → Prop)
    [DecidablePred P]
    {A B C : ℝ}
    (hP :
      (∑ a ∈ Ω.filter P,
          finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
            β H n v a) ≤ A)
    (hnot :
      (∑ a ∈ Ω.filter (fun a => ¬ P a),
          finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
            β H n v a) ≤ B)
    (hAB : A + B ≤ C) :
    (∑ a ∈ Ω,
        finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
          β H n v a) ≤ C := by
  calc
    (∑ a ∈ Ω,
        finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
          β H n v a) =
      (∑ a ∈ Ω.filter P,
        finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
          β H n v a) +
      ∑ a ∈ Ω.filter (fun a => ¬ P a),
        finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
          β H n v a :=
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSubcase_filter_add_filter_not
        β H Ω P
    _ ≤ A + B := add_le_add hP hnot
    _ ≤ C := hAB


theorem
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSubcase_sum_eq_label_sum
    (β H : ℝ) {n : ℕ} {v : FK.boxVerts 3 n}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Ω : Finset (Sigma (fun m :
      ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ =>
      finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v)))
    (label : Sigma (fun m :
      ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ =>
      finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v) → ι) :
    (∑ a ∈ Ω,
        finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
          β H n v a) =
      ∑ i : ι,
        ∑ a ∈ Ω.filter (fun a => label a = i),
          finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
            β H n v a := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := Ω) (t := (Finset.univ : Finset ι)) (g := label)
    (fun a _ha => Finset.mem_univ (label a))
    (fun a =>
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
        β H n v a)]


theorem
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSubcase_sum_le_of_label_sum_le
    (β H : ℝ) {n : ℕ} {v : FK.boxVerts 3 n}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Ω : Finset (Sigma (fun m :
      ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ =>
      finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v)))
    (label : Sigma (fun m :
      ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ =>
      finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v) → ι)
    {A : ι → ℝ} {C : ℝ}
    (hcase :
      ∀ i,
        (∑ a ∈ Ω.filter (fun a => label a = i),
            finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
              β H n v a) ≤ A i)
    (hC : (∑ i, A i) ≤ C) :
    (∑ a ∈ Ω,
        finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
          β H n v a) ≤ C := by
  calc
    (∑ a ∈ Ω,
        finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
          β H n v a) =
      ∑ i : ι,
        ∑ a ∈ Ω.filter (fun a => label a = i),
          finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
            β H n v a :=
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSubcase_sum_eq_label_sum
        β H Ω label
    _ ≤ ∑ i, A i :=
      Finset.sum_le_sum (fun i _hi => hcase i)
    _ ≤ C := hC


end Exact3D
end StatMech
