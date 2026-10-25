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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part72
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointSingletonMaxCap_pointwise
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    ∀ x ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v,
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ω v
          (finiteBoundaryGhostSourceClassEndpointMarkedSources
              v true true true ∪
            ({x} : Finset (Option (FK.boxVerts 3 n)))) ≤
        finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointSingletonMaxCap
          β H n Ω v hv := by
  intro x hx
  have hmax :=
    (Classical.choose_spec
      (finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointSingletonMaxCapPoint_exists
        β H n Ω v hv)).2 x hx
  simpa [
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointSingletonMaxCap,
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointSingletonMaxCapPoint] using
    hmax

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointSingletonMaxCap_nonneg
    {β H : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    0 ≤
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointSingletonMaxCap
        β H n Ω v hv := by
  unfold
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointSingletonMaxCap
  exact
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum_nonneg
      hβ hH n Ω v
      (finiteBoundaryGhostSourceClassEndpointMarkedSources v true true true ∪
        ({finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointSingletonMaxCapPoint
            β H n Ω v hv} : Finset (Option (FK.boxVerts 3 n))))

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution_eq_one_of_boundary
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution
        β H n Ω v =
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
        β H n Ω v true true true 1 :=
  finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution_eq_one_of_le_box_volume_sub_two
    β H n Ω v
    (finiteBoundaryGhostSourceClassEndpointMembership_one_le_box_volume_sub_two_of_boundary
      hv)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution_eq_labelFreeRawFourShare_one_of_boundary
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution
        β H n Ω v =
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
        v β H Ω true true true 1 := by
  rw [
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution_eq_one_of_boundary
      β H n Ω hv]
  symm
  exact
    SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare_eq_markedResidualExactCardImageSourceClassSum
      β H n Ω v true true true 1

end Exact3D
end StatMech
