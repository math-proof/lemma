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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part33
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipLiveBudget15.normalized_nonneg
    {B : SourceClassEndpointMembershipLiveBudget15} {D : ℝ}
    (hB : SourceClassEndpointMembershipLiveBudget15.Nonneg B)
    (hD : 0 ≤ D) :
    SourceClassEndpointMembershipLiveBudget15.Nonneg
      (SourceClassEndpointMembershipLiveBudget15.normalized B D) := by
  rcases hB with
    ⟨hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, hfourNone, hfourEndpoint,
      hfourOrigin, hfourOriginEndpoint, hfourGhost, hfourGhostEndpoint,
      hfourGhostOrigin, hfourGhostOriginEndpoint⟩
  exact
    ⟨div_nonneg hzeroNone hD, div_nonneg htwoNone hD,
      div_nonneg htwoEndpoint hD, div_nonneg htwoOrigin hD,
      div_nonneg htwoGhost hD, div_nonneg htwoGhostEndpoint hD,
      div_nonneg htwoGhostOrigin hD, div_nonneg hfourNone hD,
      div_nonneg hfourEndpoint hD, div_nonneg hfourOrigin hD,
      div_nonneg hfourOriginEndpoint hD, div_nonneg hfourGhost hD,
      div_nonneg hfourGhostEndpoint hD, div_nonneg hfourGhostOrigin hD,
      div_nonneg hfourGhostOriginEndpoint hD⟩

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipLiveBudget15.fieldwiseLeMul_normalized_of_pos
    (B : SourceClassEndpointMembershipLiveBudget15) {D : ℝ}
    (hD : 0 < D) :
    SourceClassEndpointMembershipLiveBudget15.FieldwiseLeMul
      B (SourceClassEndpointMembershipLiveBudget15.normalized B D) D := by
  refine
    ⟨le_of_eq ?_, le_of_eq ?_, le_of_eq ?_, le_of_eq ?_,
      le_of_eq ?_, le_of_eq ?_, le_of_eq ?_, le_of_eq ?_,
      le_of_eq ?_, le_of_eq ?_, le_of_eq ?_, le_of_eq ?_,
      le_of_eq ?_, le_of_eq ?_, le_of_eq ?_⟩
  · simp [SourceClassEndpointMembershipLiveBudget15.normalized, hD.ne']
  · simp [SourceClassEndpointMembershipLiveBudget15.normalized, hD.ne']
  · simp [SourceClassEndpointMembershipLiveBudget15.normalized, hD.ne']
  · simp [SourceClassEndpointMembershipLiveBudget15.normalized, hD.ne']
  · simp [SourceClassEndpointMembershipLiveBudget15.normalized, hD.ne']
  · simp [SourceClassEndpointMembershipLiveBudget15.normalized, hD.ne']
  · simp [SourceClassEndpointMembershipLiveBudget15.normalized, hD.ne']
  · simp [SourceClassEndpointMembershipLiveBudget15.normalized, hD.ne']
  · simp [SourceClassEndpointMembershipLiveBudget15.normalized, hD.ne']
  · simp [SourceClassEndpointMembershipLiveBudget15.normalized, hD.ne']
  · simp [SourceClassEndpointMembershipLiveBudget15.normalized, hD.ne']
  · simp [SourceClassEndpointMembershipLiveBudget15.normalized, hD.ne']
  · simp [SourceClassEndpointMembershipLiveBudget15.normalized, hD.ne']
  · simp [SourceClassEndpointMembershipLiveBudget15.normalized, hD.ne']
  · simp [SourceClassEndpointMembershipLiveBudget15.normalized, hD.ne']

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipLiveBudget15.normalized_total
    (B : SourceClassEndpointMembershipLiveBudget15) (D : ℝ) :
    (SourceClassEndpointMembershipLiveBudget15.normalized B D).total =
      B.total / D := by
  simp [
    SourceClassEndpointMembershipLiveBudget15.normalized,
    SourceClassEndpointMembershipLiveBudget15.total]
  ring

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipLiveBudget15.normalized_total_le_one_of_total_le
    {B : SourceClassEndpointMembershipLiveBudget15} {D : ℝ}
    (hD : 0 < D) (hB : B.total ≤ D) :
    (SourceClassEndpointMembershipLiveBudget15.normalized B D).total ≤ 1 := by
  rw [SourceClassEndpointMembershipLiveBudget15.normalized_total]
  calc
    B.total / D ≤ D / D :=
      div_le_div_of_nonneg_right hB (le_of_lt hD)
    _ = 1 := by
      field_simp [hD.ne']

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipLiveBudget15.normalized_total_lt_one_of_total_lt
    {B : SourceClassEndpointMembershipLiveBudget15} {D : ℝ}
    (hD : 0 < D) (hB : B.total < D) :
    (SourceClassEndpointMembershipLiveBudget15.normalized B D).total < 1 := by
  rw [SourceClassEndpointMembershipLiveBudget15.normalized_total]
  calc
    B.total / D < D / D :=
      div_lt_div_of_pos_right hB hD
    _ = 1 := by
      field_simp [hD.ne']

end Exact3D
end StatMech
