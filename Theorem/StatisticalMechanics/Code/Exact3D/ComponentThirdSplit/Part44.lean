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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part46
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_filter_endpointMembership_fourPlus_unmarkedResidualCard_subset_markedResidualExactCardImage
    (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool) (k : ℕ) :
    (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
      (fun S =>
        finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
            finiteBoundaryGhostSourceClassEndpointMembershipLabel
              SourceClassCardinalityCase.fourPlus
              hasGhost hasOrigin hasEndpoint ∧
          (finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v S).card =
            k) ⊆
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage
        v hasGhost hasOrigin hasEndpoint k := by
  classical
  intro S hS
  rcases Finset.mem_filter.mp hS with
    ⟨_hSsupport, hcase, hresCard⟩
  let R := finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v S
  unfold finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage
  exact Finset.mem_image.mpr
    ⟨R,
      Finset.mem_filter.mpr
        ⟨by
          simpa [R] using
            finiteBoundaryGhostSourceClassEndpointUnmarkedResidual_mem_powerset
              v S,
        by simpa [R] using hresCard⟩,
      by
        simpa [R] using
          finiteBoundaryGhostSourceClassEndpointMarkedSources_union_unmarkedResidual_eq_of_endpointMembershipCase_eq_label
            hcase⟩

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_unmarkedResidualCard_sum_le_markedResidualExactCardImageSourceClassSum
    {β H : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool) (k : ℕ) :
    (∑ S ∈
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
        (fun S =>
          finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
              finiteBoundaryGhostSourceClassEndpointMembershipLabel
                SourceClassCardinalityCase.fourPlus
                hasGhost hasOrigin hasEndpoint ∧
            (finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v S).card =
              k),
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S) ≤
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
        β H n Ω v hasGhost hasOrigin hasEndpoint k := by
  classical
  unfold
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
  exact
    Finset.sum_le_sum_of_subset_of_nonneg
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_filter_endpointMembership_fourPlus_unmarkedResidualCard_subset_markedResidualExactCardImage
        n Ω v hasGhost hasOrigin hasEndpoint k)
      (fun S _hSimage _hSnotSupport =>
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum_nonneg
          hβ hH n Ω v S)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_unmarkedResidualCard_mem_thresholdShellIndex_of_mem
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    {hasGhost hasOrigin hasEndpoint : Bool}
    {S : Finset (Option (FK.boxVerts 3 n))}
    (hS :
      S ∈
        (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
          n Ω v).filter
          (fun S =>
            finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
              finiteBoundaryGhostSourceClassEndpointMembershipLabel
                SourceClassCardinalityCase.fourPlus
                hasGhost hasOrigin hasEndpoint)) :
    (finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v S).card ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v hasGhost hasOrigin hasEndpoint := by
  classical
  let R := finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v S
  have hRpow :
      R ∈ (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset := by
    simpa [R] using
      finiteBoundaryGhostSourceClassEndpointUnmarkedResidual_mem_powerset v S
  have hRcardLe :
      R.card ≤ (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).card :=
    Finset.card_le_card (Finset.mem_powerset.mp hRpow)
  have hcase :
      finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
        finiteBoundaryGhostSourceClassEndpointMembershipLabel
          SourceClassCardinalityCase.fourPlus
          hasGhost hasOrigin hasEndpoint :=
    (Finset.mem_filter.mp hS).2
  have hunion :
      finiteBoundaryGhostSourceClassEndpointMarkedSources
          v hasGhost hasOrigin hasEndpoint ∪ R =
        S := by
    simpa [R] using
      finiteBoundaryGhostSourceClassEndpointMarkedSources_union_unmarkedResidual_eq_of_endpointMembershipCase_eq_label
        hcase
  have hcardUnion :
      S.card =
        (finiteBoundaryGhostSourceClassEndpointMarkedSources
            v hasGhost hasOrigin hasEndpoint).card + R.card := by
    have h :=
      finiteBoundaryGhostSourceClassEndpointMarkedSources_union_card_eq
        v hasGhost hasOrigin hasEndpoint hRpow
    simpa [hunion] using h
  have hfour :
      4 ≤ S.card :=
    finiteBoundaryGhostSourceClassEndpointMembershipSupportFilter_card_ge_four_of_mem
      hS rfl
  have hthresholdEq :
      finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          hasGhost hasOrigin hasEndpoint +
        (finiteBoundaryGhostSourceClassEndpointMarkedSources
          v hasGhost hasOrigin hasEndpoint).card =
        4 :=
    finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold_add_markedSources_card_eq_four_of_boundary
      hv hasGhost hasOrigin hasEndpoint
  have hthresholdLe :
      finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
        hasGhost hasOrigin hasEndpoint ≤ R.card := by
    omega
  change
    R.card ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v hasGhost hasOrigin hasEndpoint
  unfold finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hRcardLe), hthresholdLe⟩

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_filter_endpointMembership_fourPlus_eq_empty_of_boundary_of_shellIndex_eq_empty
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool)
    (hidx :
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v hasGhost hasOrigin hasEndpoint =
        ∅) :
    (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
        (fun S =>
          finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
            finiteBoundaryGhostSourceClassEndpointMembershipLabel
              SourceClassCardinalityCase.fourPlus
              hasGhost hasOrigin hasEndpoint) =
      ∅ := by
  classical
  ext S
  constructor
  · intro hS
    have hcardShell :
        (finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v S).card ∈
          finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
            v hasGhost hasOrigin hasEndpoint :=
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_unmarkedResidualCard_mem_thresholdShellIndex_of_mem
        hv hS
    rw [hidx] at hcardShell
    simp at hcardShell
  · intro hS
    simp at hS

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_filter_endpointMembership_fourPlus_eq_empty_of_boundary_of_box_volume_sub_two_lt_threshold
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool)
    (hcard :
      (2 * n + 1) ^ 3 - 2 <
        finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          hasGhost hasOrigin hasEndpoint) :
    (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
        (fun S =>
          finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
            finiteBoundaryGhostSourceClassEndpointMembershipLabel
              SourceClassCardinalityCase.fourPlus
              hasGhost hasOrigin hasEndpoint) =
      ∅ :=
  finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_filter_endpointMembership_fourPlus_eq_empty_of_boundary_of_shellIndex_eq_empty
    hv hasGhost hasOrigin hasEndpoint
    ((finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_eq_empty_iff_box_volume_sub_two_of_boundary
      hv hasGhost hasOrigin hasEndpoint).mpr hcard)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_sum_eq_unmarkedResidualCard_shell_sum
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool) :
    (∑ S ∈
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
        (fun S =>
          finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
            finiteBoundaryGhostSourceClassEndpointMembershipLabel
              SourceClassCardinalityCase.fourPlus
              hasGhost hasOrigin hasEndpoint),
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S) =
      ∑ k ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v hasGhost hasOrigin hasEndpoint,
        ∑ S ∈
          ((finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
            n Ω v).filter
            (fun S =>
              finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
                finiteBoundaryGhostSourceClassEndpointMembershipLabel
                  SourceClassCardinalityCase.fourPlus
                  hasGhost hasOrigin hasEndpoint)).filter
            (fun S =>
              (finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v S).card =
                k),
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
            β H n Ω v S := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (s :=
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
        (fun S =>
          finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
            finiteBoundaryGhostSourceClassEndpointMembershipLabel
              SourceClassCardinalityCase.fourPlus
              hasGhost hasOrigin hasEndpoint))
    (t :=
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v hasGhost hasOrigin hasEndpoint)
    (g := fun S =>
      (finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v S).card)
    (fun S hS =>
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_unmarkedResidualCard_mem_thresholdShellIndex_of_mem
        hv hS)
    (fun S =>
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S)]

end Exact3D
end StatMech
