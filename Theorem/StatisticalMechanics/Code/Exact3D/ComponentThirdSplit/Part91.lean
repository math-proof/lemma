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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part96
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem liveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsPayment_of_rowSumSchedule
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
    LiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsPayment
      label
      (liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRows
        label remainingShare tailShare) := by
  intro β _hβpos _hβc
  filter_upwards [] with n
  intro H _hH Ω v _hv
  dsimp only
  intro x _hx
  rfl

set_option linter.style.longLine false in


theorem liveSingletonOptionShareScheduleResidualCaseNormalizedLabelRows_singletonShare_eq_pointwiseRows
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
            FK.boxVerts 3 n → ℝ)
    {n : ℕ} (β H : ℝ)
    (Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) (x : Option (FK.boxVerts 3 n)) :
    (liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRows
        label remainingShare tailShare).singletonShare β H Ω v x =
      (liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRows
        remainingShare tailShare).singletonShare β H Ω v x := by
  classical
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
  let classifiedSet :=
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
      v Ω true true true ({x} : Finset (Option (FK.boxVerts 3 n)))
  have hpartition :
      (∑ i : ι Ω v x,
        ∑ E ∈
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
            v Ω true true true ({x} : Finset (Option (FK.boxVerts 3 n)))
            (label Ω v x) i,
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H E / R) =
        ∑ E ∈ classifiedSet,
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H E / R := by
    simpa [classifiedSet,
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet]
      using
        (Finset.sum_fiberwise_of_maps_to
          (s := classifiedSet)
          (t := (Finset.univ : Finset (ι Ω v x)))
          (g := label Ω v x)
          (fun E _hE => Finset.mem_univ (label Ω v x E))
          (fun E =>
            finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H E / R))
  simpa [liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRows,
    liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRows,
    cap, D, paid, R, classifiedSet] using hpartition

end Exact3D
end StatMech
