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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part70
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution_nonneg
    {β H : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    0 ≤
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution
        β H n Ω v := by
  unfold
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution
  exact Finset.sum_nonneg fun k _hk =>
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum_nonneg
      hβ hH n Ω v true true true k

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution_nonneg
    {β H : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    0 ≤
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
        β H n Ω v := by
  unfold
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
  exact Finset.sum_nonneg fun k _hk =>
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum_nonneg
      hβ hH n Ω v true true true k

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointContribution_eq_cardOne_add_tail
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointContribution
        β H n Ω v =
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution
          β H n Ω v +
        finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
          β H n Ω v := by
  unfold
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointContribution
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
  exact
    (Finset.sum_filter_add_sum_filter_not
      (Finset.Icc 1 ((2 * n + 1) ^ 3 - 2))
      (fun k => k = 1)
      (fun k =>
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
          β H n Ω v true true true k)).symm

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution_eq_sum_Icc_two
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
        β H n Ω v =
      ∑ k ∈ Finset.Icc 2 ((2 * n + 1) ^ 3 - 2),
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
          β H n Ω v true true true k := by
  unfold
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
  have htail :
      (Finset.Icc 1 ((2 * n + 1) ^ 3 - 2)).filter
          (fun k => k ≠ 1) =
        Finset.Icc 2 ((2 * n + 1) ^ 3 - 2) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hk1, hkU⟩, hkne⟩
      exact ⟨by omega, hkU⟩
    · rintro ⟨hk2, hkU⟩
      exact ⟨⟨by omega, hkU⟩, by omega⟩
  rw [htail]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution_eq_one_of_le_box_volume_sub_two
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hupper : 1 ≤ (2 * n + 1) ^ 3 - 2) :
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution
        β H n Ω v =
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
        β H n Ω v true true true 1 := by
  unfold
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution
  have hone :
      (Finset.Icc 1 ((2 * n + 1) ^ 3 - 2)).filter
          (fun k => k = 1) =
        ({1} : Finset ℕ) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨_hk1, _hkU⟩, hkone⟩
      exact hkone
    · intro hkone
      subst k
      exact ⟨⟨le_rfl, hupper⟩, rfl⟩
  rw [hone]
  simp

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembership_one_le_box_volume_sub_two_of_pos
    {n : ℕ} (hn : 0 < n) :
    1 ≤ (2 * n + 1) ^ 3 - 2 := by
  have hbase : 3 ≤ 2 * n + 1 := by omega
  have hpow : 3 ^ 3 ≤ (2 * n + 1) ^ 3 :=
    Nat.pow_le_pow_left hbase 3
  omega

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembership_one_le_box_volume_sub_two_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    1 ≤ (2 * n + 1) ^ 3 - 2 := by
  have hvbdry : FK.boxBoundary 3 n v := (Finset.mem_filter.mp hv).2
  have hn : 0 < n := by
    rw [FK.boxBoundary, Lattice.mem_vertexBoundary] at hvbdry
    by_contra hn0
    have hnz : n = 0 := Nat.eq_zero_of_not_pos hn0
    subst n
    exact hvbdry.2 hvbdry.1
  exact finiteBoundaryGhostSourceClassEndpointMembership_one_le_box_volume_sub_two_of_pos
    hn

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointUnmarkedOptions_nonempty_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).Nonempty := by
  apply Finset.card_pos.mp
  rw [
    finiteBoundaryGhostSourceClassEndpointUnmarkedOptions_card_eq_box_volume_sub_two_of_boundary
      hv]
  have hle :
      1 ≤ (2 * n + 1) ^ 3 - 2 :=
    finiteBoundaryGhostSourceClassEndpointMembership_one_le_box_volume_sub_two_of_boundary
      hv
  omega

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointSingletonMaxCapPoint_exists
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    ∃ x,
      x ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v ∧
        ∀ y ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v,
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
              β H n Ω v
              (finiteBoundaryGhostSourceClassEndpointMarkedSources
                  v true true true ∪
                ({y} : Finset (Option (FK.boxVerts 3 n)))) ≤
            finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
              β H n Ω v
              (finiteBoundaryGhostSourceClassEndpointMarkedSources
                  v true true true ∪
                ({x} : Finset (Option (FK.boxVerts 3 n)))) := by
  exact
    Finset.exists_max_image
      (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v)
      (fun x =>
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ω v
          (finiteBoundaryGhostSourceClassEndpointMarkedSources v true true true ∪
            ({x} : Finset (Option (FK.boxVerts 3 n)))))
      (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions_nonempty_of_boundary
        hv)

end Exact3D
end StatMech
