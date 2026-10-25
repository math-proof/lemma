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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part18
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold_false_false_false :
    finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
      false false false = 4 := rfl

set_option linter.style.longLine false in

theorem finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold_false_false_true :
    finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
      false false true = 3 := rfl

set_option linter.style.longLine false in

theorem finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold_false_true_false :
    finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
      false true false = 3 := rfl

set_option linter.style.longLine false in

theorem finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold_false_true_true :
    finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
      false true true = 2 := rfl

set_option linter.style.longLine false in

theorem finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold_true_false_false :
    finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
      true false false = 3 := rfl

set_option linter.style.longLine false in

theorem finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold_true_false_true :
    finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
      true false true = 2 := rfl

set_option linter.style.longLine false in

theorem finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold_true_true_false :
    finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
      true true false = 2 := rfl

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold_true_true_true :
    finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
      true true true = 1 := rfl

set_option linter.style.longLine false in

theorem finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold_pos
    (hasGhost hasOrigin hasEndpoint : Bool) :
    0 <
      finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
        hasGhost hasOrigin hasEndpoint := by
  cases hasGhost <;> cases hasOrigin <;> cases hasEndpoint <;>
    simp [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold]

set_option linter.style.longLine false in

theorem finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold_le_four
    (hasGhost hasOrigin hasEndpoint : Bool) :
    finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
        hasGhost hasOrigin hasEndpoint ≤
      4 := by
  cases hasGhost <;> cases hasOrigin <;> cases hasEndpoint <;>
    simp [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMarkedSources_disjoint_unmarkedOptions
    {n : ℕ} (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool) :
    Disjoint
      (finiteBoundaryGhostSourceClassEndpointMarkedSources
        v hasGhost hasOrigin hasEndpoint)
      (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v) := by
  classical
  rw [Finset.disjoint_left]
  intro x hxmarked hxunmarked
  have hxU :=
    finiteBoundaryGhostSourceClassEndpointUnmarkedOptions_mem_iff.mp
      hxunmarked
  rcases
      finiteBoundaryGhostSourceClassEndpointMarkedSources_mem_iff.mp
        hxmarked with
    hghost | horigin | hendpoint
  · exact hxU.1 hghost.1
  · exact hxU.2.1 horigin.1
  · exact hxU.2.2 hendpoint.1

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMarkedSources_union_card_eq
    {n : ℕ} (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool)
    {R : Finset (Option (FK.boxVerts 3 n))}
    (hR :
      R ∈ (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset) :
    (finiteBoundaryGhostSourceClassEndpointMarkedSources
        v hasGhost hasOrigin hasEndpoint ∪ R).card =
      (finiteBoundaryGhostSourceClassEndpointMarkedSources
        v hasGhost hasOrigin hasEndpoint).card + R.card := by
  classical
  exact Finset.card_union_of_disjoint
    (by
      rw [Finset.disjoint_left]
      intro x hxmarked hxR
      have hxnot :=
        (Finset.disjoint_left.mp
          (finiteBoundaryGhostSourceClassEndpointMarkedSources_disjoint_unmarkedOptions
            v hasGhost hasOrigin hasEndpoint)) hxmarked
      exact hxnot ((Finset.mem_powerset.mp hR) hxR))

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold_add_markedSources_card_eq_four_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool) :
    finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
        hasGhost hasOrigin hasEndpoint +
      (finiteBoundaryGhostSourceClassEndpointMarkedSources
        v hasGhost hasOrigin hasEndpoint).card =
      4 := by
  classical
  have hvbdry : FK.boxBoundary 3 n v := (Finset.mem_filter.mp hv).2
  have horigin_ne_v : IsingFK.boxOrigin 3 n ≠ v :=
    boxOrigin_ne_of_boxBoundary 3 n hvbdry
  cases hasGhost <;> cases hasOrigin <;> cases hasEndpoint
  · simp [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold,
      finiteBoundaryGhostSourceClassEndpointMarkedSources]
  · have hset :
        finiteBoundaryGhostSourceClassEndpointMarkedSources
            v false false true =
          ({some v} : Finset (Option (FK.boxVerts 3 n))) := by
      ext x
      simp [finiteBoundaryGhostSourceClassEndpointMarkedSources]
    simp [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold, hset]
  · have hset :
        finiteBoundaryGhostSourceClassEndpointMarkedSources
            v false true false =
          ({some (IsingFK.boxOrigin 3 n)} :
            Finset (Option (FK.boxVerts 3 n))) := by
      ext x
      simp [finiteBoundaryGhostSourceClassEndpointMarkedSources]
    simp [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold, hset]
  · have hset :
        finiteBoundaryGhostSourceClassEndpointMarkedSources
            v false true true =
          ({some (IsingFK.boxOrigin 3 n), some v} :
            Finset (Option (FK.boxVerts 3 n))) := by
      ext x
      simp [finiteBoundaryGhostSourceClassEndpointMarkedSources]
    simp [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold,
      hset, horigin_ne_v]
  · have hset :
        finiteBoundaryGhostSourceClassEndpointMarkedSources
            v true false false =
          ({none} : Finset (Option (FK.boxVerts 3 n))) := by
      ext x
      simp [finiteBoundaryGhostSourceClassEndpointMarkedSources]
    simp [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold, hset]
  · have hset :
        finiteBoundaryGhostSourceClassEndpointMarkedSources
            v true false true =
          ({none, some v} : Finset (Option (FK.boxVerts 3 n))) := by
      ext x
      simp [finiteBoundaryGhostSourceClassEndpointMarkedSources]
    simp [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold, hset]
  · have hset :
        finiteBoundaryGhostSourceClassEndpointMarkedSources
            v true true false =
          ({none, some (IsingFK.boxOrigin 3 n)} :
            Finset (Option (FK.boxVerts 3 n))) := by
      ext x
      simp [finiteBoundaryGhostSourceClassEndpointMarkedSources]
    simp [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold, hset]
  · have hset :
        finiteBoundaryGhostSourceClassEndpointMarkedSources
            v true true true =
          ({none, some (IsingFK.boxOrigin 3 n), some v} :
            Finset (Option (FK.boxVerts 3 n))) := by
      ext x
      simp [finiteBoundaryGhostSourceClassEndpointMarkedSources]
    simp [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold,
      hset, horigin_ne_v]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointUnmarkedOptions_powerset_filter_markedResidualCard_eq_threshold
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool) :
    ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
      (fun R =>
        4 ≤
          (finiteBoundaryGhostSourceClassEndpointMarkedSources
            v hasGhost hasOrigin hasEndpoint ∪ R).card)) =
      ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
        (fun R =>
          finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
            hasGhost hasOrigin hasEndpoint ≤ R.card)) := by
  classical
  apply Finset.filter_congr
  intro R hR
  have hcardUnion :=
    finiteBoundaryGhostSourceClassEndpointMarkedSources_union_card_eq
      v hasGhost hasOrigin hasEndpoint hR
  have hthreshold :=
    finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold_add_markedSources_card_eq_four_of_boundary
      hv hasGhost hasOrigin hasEndpoint
  constructor <;> intro h <;> omega

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_zero_none_sum_le_emptySourceClassSum
    {β H : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    (∑ S ∈
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
        (fun S =>
          finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
            finiteBoundaryGhostSourceClassEndpointMembershipLabel
              SourceClassCardinalityCase.zero false false false),
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S) ≤
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v ∅ := by
  rw [
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_zero_none_sum_eq_emptySourceClassSum]
  by_cases hmem :
      (∅ : Finset (Option (FK.boxVerts 3 n))) ∈
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
          n Ω v
  · simp [hmem]
  · simpa [hmem] using
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum_nonneg
        hβ hH n Ω v
        (∅ : Finset (Option (FK.boxVerts 3 n)))

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_two_ghost_endpoint_sum_le_pairSourceClassSum
    {β H : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    (∑ S ∈
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
        (fun S =>
          finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
            finiteBoundaryGhostSourceClassEndpointMembershipLabel
              SourceClassCardinalityCase.two true false true),
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S) ≤
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v ({none, some v} : Finset (Option (FK.boxVerts 3 n))) := by
  rw [
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_two_ghost_endpoint_sum_eq_pairSourceClassSum
      β H n Ω v hv]
  by_cases hmem :
      ({none, some v} : Finset (Option (FK.boxVerts 3 n))) ∈
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
          n Ω v
  · simp [hmem]
  · simpa [hmem] using
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum_nonneg
        hβ hH n Ω v
        ({none, some v} : Finset (Option (FK.boxVerts 3 n)))

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_two_ghost_origin_sum_le_pairSourceClassSum
    {β H : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    (∑ S ∈
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
        (fun S =>
          finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
            finiteBoundaryGhostSourceClassEndpointMembershipLabel
              SourceClassCardinalityCase.two true true false),
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S) ≤
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v
        ({none, some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n))) := by
  rw [
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_two_ghost_origin_sum_eq_pairSourceClassSum
      β H n Ω v hv]
  by_cases hmem :
      ({none, some (IsingFK.boxOrigin 3 n)} :
        Finset (Option (FK.boxVerts 3 n))) ∈
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
          n Ω v
  · simp [hmem]
  · simpa [hmem] using
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum_nonneg
        hβ hH n Ω v
        ({none, some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n)))

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_two_endpoint_sum_le_unmarkedPairImageSum
    {β H : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    (∑ S ∈
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
        (fun S =>
          finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
            finiteBoundaryGhostSourceClassEndpointMembershipLabel
              SourceClassCardinalityCase.two false false true),
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S) ≤
      ∑ S ∈
        (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).image
          (fun x => ({some v, x} : Finset (Option (FK.boxVerts 3 n)))),
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ω v S := by
  classical
  exact
    Finset.sum_le_sum_of_subset_of_nonneg
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_filter_endpointMembership_two_endpoint_subset_unmarkedPairImage
        n Ω v)
      (fun S _hSimage _hSnotCell =>
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum_nonneg
          hβ hH n Ω v S)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_two_origin_sum_le_unmarkedPairImageSum
    {β H : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    (∑ S ∈
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
        (fun S =>
          finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
            finiteBoundaryGhostSourceClassEndpointMembershipLabel
              SourceClassCardinalityCase.two false true false),
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S) ≤
      ∑ S ∈
        (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).image
          (fun x =>
            ({some (IsingFK.boxOrigin 3 n), x} :
              Finset (Option (FK.boxVerts 3 n)))),
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ω v S := by
  classical
  exact
    Finset.sum_le_sum_of_subset_of_nonneg
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_filter_endpointMembership_two_origin_subset_unmarkedPairImage
        n Ω v)
      (fun S _hSimage _hSnotCell =>
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum_nonneg
          hβ hH n Ω v S)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_two_ghost_sum_le_unmarkedPairImageSum
    {β H : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    (∑ S ∈
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
        (fun S =>
          finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
            finiteBoundaryGhostSourceClassEndpointMembershipLabel
              SourceClassCardinalityCase.two true false false),
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S) ≤
      ∑ S ∈
        (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).image
          (fun x => ({none, x} : Finset (Option (FK.boxVerts 3 n)))),
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ω v S := by
  classical
  exact
    Finset.sum_le_sum_of_subset_of_nonneg
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_filter_endpointMembership_two_ghost_subset_unmarkedPairImage
        n Ω v)
      (fun S _hSimage _hSnotCell =>
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum_nonneg
          hβ hH n Ω v S)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_two_none_sum_le_unmarkedPairImageSum
    {β H : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    (∑ S ∈
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
        (fun S =>
          finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
            finiteBoundaryGhostSourceClassEndpointMembershipLabel
              SourceClassCardinalityCase.two false false false),
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S) ≤
      ∑ S ∈
        Finset.image₂
          (fun x y => ({x, y} : Finset (Option (FK.boxVerts 3 n))))
          (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v)
          (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v),
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ω v S := by
  classical
  exact
    Finset.sum_le_sum_of_subset_of_nonneg
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_filter_endpointMembership_two_none_subset_unmarkedPairImage
        n Ω v)
      (fun S _hSimage _hSnotCell =>
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum_nonneg
          hβ hH n Ω v S)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum_eq_sourceClassSupport_sum
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
        β H n Ω v =
      ∑ S ∈
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
            n Ω v,
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ω v S := by
  classical
  rw [
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum_eq_support_sum]
  unfold finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
  rw [← Finset.sum_fiberwise_of_maps_to
    (s :=
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSupport
        n Ω v)
    (t :=
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSupport
        n Ω v).image (fun D => D.1))
    (g := fun D => D.1)
    (fun D hD => Finset.mem_image.mpr ⟨D, hD, rfl⟩)
    (fun D => finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H D)]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum_eq_sourceClassSupport_filter_add_filter_not
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (P : Finset (Option (FK.boxVerts 3 n)) → Prop)
    [DecidablePred P] :
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
        β H n Ω v =
      (∑ S ∈
          (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
            n Ω v).filter P,
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
            β H n Ω v S) +
        ∑ S ∈
          (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
            n Ω v).filter (fun S => ¬ P S),
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
            β H n Ω v S := by
  classical
  rw [
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum_eq_sourceClassSupport_sum]
  exact
    (Finset.sum_filter_add_sum_filter_not
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v)
      P
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v)).symm

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum_le_of_sourceClassSupport_filter_le_filter_not_le
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (P : Finset (Option (FK.boxVerts 3 n)) → Prop)
    [DecidablePred P]
    {A B C : ℝ}
    (hP :
      (∑ S ∈
          (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
            n Ω v).filter P,
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
            β H n Ω v S) ≤
        A)
    (hnot :
      (∑ S ∈
          (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
            n Ω v).filter (fun S => ¬ P S),
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
            β H n Ω v S) ≤
        B)
    (hAB : A + B ≤ C) :
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
        β H n Ω v ≤ C := by
  calc
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
        β H n Ω v =
      (∑ S ∈
          (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
            n Ω v).filter P,
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
            β H n Ω v S) +
        ∑ S ∈
          (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
            n Ω v).filter (fun S => ¬ P S),
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
            β H n Ω v S :=
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum_eq_sourceClassSupport_filter_add_filter_not
        β H n Ω v P
    _ ≤ A + B := add_le_add hP hnot
    _ ≤ C := hAB

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum_eq_sourceClassSupport_label_sum
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (label : Finset (Option (FK.boxVerts 3 n)) → ι) :
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
        β H n Ω v =
      ∑ i : ι,
        ∑ S ∈
          (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
            n Ω v).filter (fun S => label S = i),
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
            β H n Ω v S := by
  classical
  rw [
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum_eq_sourceClassSupport_sum]
  rw [← Finset.sum_fiberwise_of_maps_to
    (s :=
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v)
    (t := (Finset.univ : Finset ι)) (g := label)
    (fun S _hS => Finset.mem_univ (label S))
    (fun S =>
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S)]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum_le_of_sourceClassSupport_label_sum_le
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (label : Finset (Option (FK.boxVerts 3 n)) → ι)
    {A : ι → ℝ} {C : ℝ}
    (hcase :
      ∀ i,
        (∑ S ∈
          (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
            n Ω v).filter (fun S => label S = i),
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
            β H n Ω v S) ≤
          A i)
    (hC : (∑ i, A i) ≤ C) :
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
        β H n Ω v ≤ C := by
  calc
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
        β H n Ω v =
      ∑ i : ι,
        ∑ S ∈
          (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
            n Ω v).filter (fun S => label S = i),
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
            β H n Ω v S :=
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum_eq_sourceClassSupport_label_sum
        β H n Ω v label
    _ ≤ ∑ i, A i :=
      Finset.sum_le_sum (fun i _hi => hcase i)
    _ ≤ C := hC

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum_eq_sourceClassSupport_liveEndpointMembership_sum
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
        β H n Ω v =
      ∑ c ∈ finiteBoundaryGhostSourceClassEndpointMembershipLiveCaseFinset,
        ∑ S ∈
          (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
            n Ω v).filter
            (fun S =>
              finiteBoundaryGhostSourceClassEndpointMembershipCase v S = c),
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
            β H n Ω v S := by
  classical
  rw [
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum_eq_sourceClassSupport_label_sum
      β H n Ω v
      (fun S => finiteBoundaryGhostSourceClassEndpointMembershipCase v S)]
  rw [
    finiteBoundaryGhostSourceClassEndpointMembershipLiveCaseFinset_eq_filter]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro c _hc
  by_cases hlive :
      finiteBoundaryGhostSourceClassEndpointMembershipLiveCase c
  · simp [hlive]
  · have hzero :
        (∑ S ∈
          (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
            n Ω v).filter
            (fun S =>
              finiteBoundaryGhostSourceClassEndpointMembershipCase v S = c),
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
            β H n Ω v S) = 0 :=
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_not_live_sum_eq_zero
        β H n Ω v hv c hlive
    simp [hlive, hzero]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum_le_of_sourceClassSupport_liveEndpointMembership_sum_le
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    {A : SourceClassEndpointMembershipCase → ℝ} {C : ℝ}
    (hcase :
      ∀ c,
        c ∈ finiteBoundaryGhostSourceClassEndpointMembershipLiveCaseFinset →
          (∑ S ∈
            (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
              n Ω v).filter
              (fun S =>
                finiteBoundaryGhostSourceClassEndpointMembershipCase v S = c),
            finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
              β H n Ω v S) ≤
            A c)
    (hC :
      (∑ c ∈ finiteBoundaryGhostSourceClassEndpointMembershipLiveCaseFinset,
        A c) ≤ C) :
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
        β H n Ω v ≤ C := by
  calc
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
        β H n Ω v =
      ∑ c ∈ finiteBoundaryGhostSourceClassEndpointMembershipLiveCaseFinset,
        ∑ S ∈
          (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
            n Ω v).filter
            (fun S =>
              finiteBoundaryGhostSourceClassEndpointMembershipCase v S = c),
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
            β H n Ω v S :=
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum_eq_sourceClassSupport_liveEndpointMembership_sum
        β H n Ω v hv
    _ ≤ ∑ c ∈ finiteBoundaryGhostSourceClassEndpointMembershipLiveCaseFinset,
        A c :=
      Finset.sum_le_sum (fun c hc => hcase c hc)
    _ ≤ C := hC

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum_eq_sourceClassSupport_ghostMembership_add_nonGhostMembership
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
        β H n Ω v =
      (∑ S ∈
          (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
            n Ω v).filter (fun S => none ∈ S),
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
            β H n Ω v S) +
        ∑ S ∈
          (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
            n Ω v).filter (fun S => none ∉ S),
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
            β H n Ω v S := by
  classical
  simpa using
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum_eq_sourceClassSupport_filter_add_filter_not
      β H n Ω v (fun S => none ∈ S)

end Exact3D
end StatMech
