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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part17
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipLiveCaseFinset_mem_iff
    (c : SourceClassEndpointMembershipCase) :
    c ∈ finiteBoundaryGhostSourceClassEndpointMembershipLiveCaseFinset ↔
      finiteBoundaryGhostSourceClassEndpointMembershipLiveCase c := by
  rcases c with ⟨cardCase, hasGhost, hasOrigin, hasEndpoint⟩
  cases cardCase <;>
    cases hasGhost <;>
    cases hasOrigin <;>
    cases hasEndpoint <;>
    simp [
      finiteBoundaryGhostSourceClassEndpointMembershipLiveCaseFinset,
      finiteBoundaryGhostSourceClassEndpointMembershipLabel,
      finiteBoundaryGhostSourceClassEndpointMembershipLiveCase,
      finiteBoundaryGhostSourceClassEndpointMembershipZeroEmptyCase,
      finiteBoundaryGhostSourceClassEndpointMembershipTwoOriginEndpointNoGhostCase,
      finiteBoundaryGhostSourceClassEndpointMembershipTwoOriginEndpointGhostCase]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipLiveCaseFinset_eq_filter :
    finiteBoundaryGhostSourceClassEndpointMembershipLiveCaseFinset =
      (Finset.univ : Finset SourceClassEndpointMembershipCase).filter
        finiteBoundaryGhostSourceClassEndpointMembershipLiveCase := by
  ext c
  simp [
    finiteBoundaryGhostSourceClassEndpointMembershipLiveCaseFinset_mem_iff]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipLiveCaseFinset_card :
    finiteBoundaryGhostSourceClassEndpointMembershipLiveCaseFinset.card = 15 := by
  decide

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_not_live_sum_eq_zero
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (c : SourceClassEndpointMembershipCase)
    (hdead : ¬ finiteBoundaryGhostSourceClassEndpointMembershipLiveCase c) :
    (∑ S ∈
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
        (fun S => finiteBoundaryGhostSourceClassEndpointMembershipCase v S = c),
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S) = 0 := by
  classical
  by_cases hczero : c.cardCase = SourceClassCardinalityCase.zero
  · by_cases hcempty :
        c = finiteBoundaryGhostSourceClassEndpointMembershipZeroEmptyCase
    · exfalso
      apply hdead
      refine ⟨Or.inr hcempty, ?_, ?_⟩
      · intro hc
        have hcard :
            (finiteBoundaryGhostSourceClassEndpointMembershipZeroEmptyCase).cardCase =
              SourceClassCardinalityCase.two := by
          simpa [hcempty] using
            congrArg SourceClassEndpointMembershipCase.cardCase hc
        simp [finiteBoundaryGhostSourceClassEndpointMembershipZeroEmptyCase] at hcard
      · intro hc
        have hcard :
            (finiteBoundaryGhostSourceClassEndpointMembershipZeroEmptyCase).cardCase =
              SourceClassCardinalityCase.two := by
          simpa [hcempty] using
            congrArg SourceClassEndpointMembershipCase.cardCase hc
        simp [finiteBoundaryGhostSourceClassEndpointMembershipZeroEmptyCase] at hcard
    · exact
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_zero_ne_emptyCase_sum_eq_zero
          β H n Ω v c hczero hcempty
  · by_cases hcNoGhost :
        c = finiteBoundaryGhostSourceClassEndpointMembershipTwoOriginEndpointNoGhostCase
    · subst c
      exact
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_two_origin_endpoint_noGhost_sum_eq_zero
          β H n Ω v hv
    · by_cases hcGhost :
        c = finiteBoundaryGhostSourceClassEndpointMembershipTwoOriginEndpointGhostCase
      · subst c
        exact
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_two_origin_endpoint_ghost_sum_eq_zero
            β H n Ω v hv
      · exfalso
        exact hdead ⟨Or.inl hczero, hcNoGhost, hcGhost⟩

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum_nonneg
    {β H : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (S : Finset (Option (FK.boxVerts 3 n))) :
    0 ≤
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S := by
  classical
  unfold finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
  refine Finset.sum_nonneg ?_
  intro D _hD
  exact
    mul_nonneg (Nat.cast_nonneg _)
      (finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceDataWeight_nonneg
        hβ hH D)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_sum_le_markedResidualImageSum
    {β H : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (cardCase : SourceClassCardinalityCase)
    (hasGhost hasOrigin hasEndpoint : Bool) :
    (∑ S ∈
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
        (fun S =>
          finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
            finiteBoundaryGhostSourceClassEndpointMembershipLabel
              cardCase hasGhost hasOrigin hasEndpoint),
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S) ≤
      ∑ S ∈
        (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.image
          (fun R =>
            finiteBoundaryGhostSourceClassEndpointMarkedSources
                v hasGhost hasOrigin hasEndpoint ∪ R),
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ω v S := by
  classical
  exact
    Finset.sum_le_sum_of_subset_of_nonneg
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_filter_endpointMembership_subset_markedResidualImage
        n Ω v cardCase hasGhost hasOrigin hasEndpoint)
      (fun S _hSimage _hSnotCell =>
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum_nonneg
          hβ hH n Ω v S)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_sum_le_markedResidualCardImageSum
    {β H : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
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
        β H n Ω v S) ≤
      ∑ S ∈
        ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
          (fun R =>
            4 ≤
              (finiteBoundaryGhostSourceClassEndpointMarkedSources
                  v hasGhost hasOrigin hasEndpoint ∪ R).card)).image
          (fun R =>
            finiteBoundaryGhostSourceClassEndpointMarkedSources
                v hasGhost hasOrigin hasEndpoint ∪ R),
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ω v S := by
  classical
  exact
    Finset.sum_le_sum_of_subset_of_nonneg
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_filter_endpointMembership_fourPlus_subset_markedResidualCardImage
        n Ω v hasGhost hasOrigin hasEndpoint)
      (fun S _hSimage _hSnotCell =>
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum_nonneg
          hβ hH n Ω v S)

end Exact3D
end StatMech
