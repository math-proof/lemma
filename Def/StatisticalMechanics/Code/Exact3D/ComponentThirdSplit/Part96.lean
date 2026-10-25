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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part90
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRows
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
              ι Ω v x)
    (remainingShare tailShare :
      ∀ {n : ℕ},
        ℝ → ℝ →
          Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
            FK.boxVerts 3 n → ℝ) :
    LiveSingletonOptionShareSchedule where
  remainingShare := remainingShare
  tailShare := tailShare
  singletonShare := fun {n} β H Ω v x =>
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
    ∑ i : ι Ω v x,
      ∑ E ∈
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
          v Ω true true true
          ({x} : Finset (Option (FK.boxVerts 3 n)))
          (label Ω v x) i,
        finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H E / R

end Exact3D
end StatMech
