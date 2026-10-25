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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part38
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_mem_iff
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool} {k : ℕ}
    {S : Finset (Option (FK.boxVerts 3 n))} :
    S ∈
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet
          n Ω v hasGhost hasOrigin hasEndpoint k ↔
      S ∈
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
            n Ω v ∧
        finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
            finiteBoundaryGhostSourceClassEndpointMembershipLabel
              SourceClassCardinalityCase.fourPlus
              hasGhost hasOrigin hasEndpoint ∧
        (finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v S).card =
          k := by
  simp [
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_subset_sourceClassSupport
    (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool) (k : ℕ) :
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet
        n Ω v hasGhost hasOrigin hasEndpoint k ⊆
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v := by
  intro S hS
  exact
    (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_mem_iff.mp
      hS).1

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_membershipCase_eq
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool} {k : ℕ}
    {S : Finset (Option (FK.boxVerts 3 n))}
    (hS :
      S ∈
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet
          n Ω v hasGhost hasOrigin hasEndpoint k) :
    finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
      finiteBoundaryGhostSourceClassEndpointMembershipLabel
        SourceClassCardinalityCase.fourPlus
        hasGhost hasOrigin hasEndpoint :=
  (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_mem_iff.mp
    hS).2.1

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_unmarkedResidual_card_eq
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool} {k : ℕ}
    {S : Finset (Option (FK.boxVerts 3 n))}
    (hS :
      S ∈
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet
          n Ω v hasGhost hasOrigin hasEndpoint k) :
    (finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v S).card = k :=
  (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_mem_iff.mp
    hS).2.2

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_eq_empty_of_unmarkedOptions_card_lt
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    (hasGhost hasOrigin hasEndpoint : Bool) {k : ℕ}
    (hk :
      (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).card < k) :
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet
        n Ω v hasGhost hasOrigin hasEndpoint k =
      ∅ := by
  classical
  ext S
  constructor
  · intro hS
    have hres :
        (finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v S).card =
          k :=
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_unmarkedResidual_card_eq
        hS
    have hpow :
        finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v S ∈
          (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset :=
      finiteBoundaryGhostSourceClassEndpointUnmarkedResidual_mem_powerset v S
    have hle :
        (finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v S).card ≤
          (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).card :=
      Finset.card_le_card (Finset.mem_powerset.mp hpow)
    omega
  · intro hS
    simp at hS

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum_eq_zero_of_unmarkedOptions_card_lt
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool) {k : ℕ}
    (hk :
      (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).card < k) :
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum
        β H n Ω v hasGhost hasOrigin hasEndpoint k =
      0 := by
  unfold finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum
  rw [
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_eq_empty_of_unmarkedOptions_card_lt
      hasGhost hasOrigin hasEndpoint hk]
  simp

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_eq_empty_of_boundary_of_box_volume_sub_two_lt
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool) {k : ℕ}
    (hk : (2 * n + 1) ^ 3 - 2 < k) :
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet
        n Ω v hasGhost hasOrigin hasEndpoint k =
      ∅ :=
  finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_eq_empty_of_unmarkedOptions_card_lt
    hasGhost hasOrigin hasEndpoint
    (by
      rw [
        finiteBoundaryGhostSourceClassEndpointUnmarkedOptions_card_eq_boxVerts_card_sub_two_of_boundary
          hv,
        StatMech.FK.ecz_boxVerts_card]
      exact hk)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum_eq_zero_of_boundary_of_box_volume_sub_two_lt
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool) {k : ℕ}
    (hk : (2 * n + 1) ^ 3 - 2 < k) :
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum
        β H n Ω v hasGhost hasOrigin hasEndpoint k =
      0 :=
  finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum_eq_zero_of_unmarkedOptions_card_lt
    β H n Ω v hasGhost hasOrigin hasEndpoint
    (by
      rw [
        finiteBoundaryGhostSourceClassEndpointUnmarkedOptions_card_eq_boxVerts_card_sub_two_of_boundary
          hv,
        StatMech.FK.ecz_boxVerts_card]
      exact hk)

end Exact3D
end StatMech
