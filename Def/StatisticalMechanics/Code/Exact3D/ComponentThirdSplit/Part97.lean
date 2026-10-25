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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part91
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def liveSingletonOptionNormalizedRemainingShare
    {n : ℕ} (β H : ℝ)
    (Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) : ℝ :=
  let cap := boundaryCrossingCap n Ω
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let paid :=
    cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n +
      cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
          β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let R := D - paid
  finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
    β H n Ω v / R

set_option linter.style.longLine false in


noncomputable def liveSingletonOptionNormalizedTailShare
    {n : ℕ} (β H : ℝ)
    (Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) : ℝ :=
  let cap := boundaryCrossingCap n Ω
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let paid :=
    cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n +
      cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
          β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let R := D - paid
  finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
    β H n Ω v / R

set_option linter.style.longLine false in


noncomputable def liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical :
    LiveSingletonOptionShareSchedule :=
  liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRows
    (fun {n} β H Ω v =>
      liveSingletonOptionNormalizedRemainingShare (n := n) β H Ω v)
    (fun {n} β H Ω v =>
      liveSingletonOptionNormalizedTailShare (n := n) β H Ω v)

set_option linter.style.longLine false in


noncomputable def liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical
    {ι :
      {n : ℕ} →
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
          FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
    [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
    [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
    (label :
      ∀ {n : ℕ},
        (Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) →
          (v : FK.boxVerts 3 n) →
          (x : Option (FK.boxVerts 3 n)) →
            finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
              n v →
              ι Ω v x) :
    LiveSingletonOptionShareSchedule :=
  liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRows
    label
    (fun {n} β H Ω v =>
      liveSingletonOptionNormalizedRemainingShare (n := n) β H Ω v)
    (fun {n} β H Ω v =>
      liveSingletonOptionNormalizedTailShare (n := n) β H Ω v)

end Exact3D
end StatMech
