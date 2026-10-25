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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part110
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderMajorantShareAbsorptionPositiveSubcritical
    (ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*)
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    (label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R) :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let cap := boundaryCrossingCap n Ωnz
            let D :=
              finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
            let R :=
              D -
                (cap *
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                      β H n +
                  cap *
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                      β H n v +
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                    β H n v)
            let rawBudget :=
              SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15
                v β H Ωnz (ι n v) (label Ωnz v)
            ∃ B : SourceClassEndpointMembershipLiveBudget15,
              0 < R ∧
              SourceClassEndpointMembershipLiveBudget15.FieldwiseLe
                rawBudget B ∧
              B.total ≤ R

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellMajorantShareAbsorptionPositiveSubcritical
    (ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*)
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    (label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R) :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let cap := boundaryCrossingCap n Ωnz
            let D :=
              finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
            let R :=
              D -
                (cap *
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                      β H n +
                  cap *
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                      β H n v +
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                    β H n v)
            ∃ shellMajorant :
                SourceClassEndpointMembershipResidualShellShare15 v,
              0 < R ∧
              shellMajorant.RawFieldwiseLe
                β H Ωnz (ι n v) (label Ωnz v) ∧
              shellMajorant.total ≤ R

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellMajorantDenominatorFreeAbsorptionPositiveSubcritical
    (ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*)
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    (label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R) :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let cap := boundaryCrossingCap n Ωnz
            let D :=
              finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
            ∃ shellMajorant :
                SourceClassEndpointMembershipResidualShellShare15 v,
              shellMajorant.RawFieldwiseLe
                β H Ωnz (ι n v) (label Ωnz v) ∧
              cap *
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                      β H n +
                  cap *
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                      β H n v +
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                    β H n v +
                  shellMajorant.total ≤ D

end Exact3D
end StatMech
