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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part101
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
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
            let rawBudget :=
              SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15
                v β H Ωnz (ι n v) (label Ωnz v)
            ∃ B : SourceClassEndpointMembershipLiveBudget15,
              SourceClassEndpointMembershipLiveBudget15.FieldwiseLe
                rawBudget B ∧
              cap *
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                      β H n +
                  cap *
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                      β H n v +
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                    β H n v +
                  B.total < D

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
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
                  shellMajorant.total < D

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
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
            ∃ zero_none two_none two_endpoint two_origin two_ghost
                two_ghost_endpoint two_ghost_origin : ℝ,
              ∃ fourMajorant : Bool → Bool → Bool → ℕ → ℝ,
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).zero_none ≤ zero_none ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_none ≤ two_none ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_endpoint ≤ two_endpoint ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_origin ≤ two_origin ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost ≤ two_ghost ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost_endpoint ≤
                  two_ghost_endpoint ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost_origin ≤ two_ghost_origin ∧
                (∀ hasGhost hasOrigin hasEndpoint k,
                  k ∈
                      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
                        v hasGhost hasOrigin hasEndpoint →
                    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
                      v β H Ωnz (ι n v) (label Ωnz v)
                        hasGhost hasOrigin hasEndpoint k ≤
                      fourMajorant hasGhost hasOrigin hasEndpoint k) ∧
                cap *
                      finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                        β H n +
                    cap *
                      finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                        β H n v +
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                      β H n v +
                    (SourceClassEndpointMembershipResidualShellShare15.ofFourShare
                      v zero_none two_none two_endpoint two_origin two_ghost
                      two_ghost_endpoint two_ghost_origin
                      fourMajorant).total < D

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitRowStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
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
            ∃ zero_none two_none two_endpoint two_origin two_ghost
                two_ghost_endpoint two_ghost_origin : ℝ,
              ∃ rowMajorant :
                  ∀ hasGhost hasOrigin hasEndpoint
                    (R : Finset (Option (FK.boxVerts 3 n))),
                    ι n v hasGhost hasOrigin hasEndpoint R → ℝ,
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).zero_none ≤ zero_none ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_none ≤ two_none ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_endpoint ≤ two_endpoint ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_origin ≤ two_origin ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost ≤ two_ghost ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost_endpoint ≤
                  two_ghost_endpoint ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost_origin ≤ two_ghost_origin ∧
                (∀ hasGhost hasOrigin hasEndpoint k,
                  k ∈
                      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
                        v hasGhost hasOrigin hasEndpoint →
                    ∀ R,
                      R ∈
                          finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                            v k →
                        ∀ i :
                          ι n v hasGhost hasOrigin hasEndpoint R,
                          (∑ E ∈
                            finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
                              v Ωnz hasGhost hasOrigin hasEndpoint R
                              (label Ωnz v hasGhost hasOrigin hasEndpoint R)
                              i,
                            finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                              β H E) ≤
                            rowMajorant hasGhost hasOrigin hasEndpoint R i) ∧
                (let fourMajorant : Bool → Bool → Bool → ℕ → ℝ :=
                    fun hasGhost hasOrigin hasEndpoint k =>
                      ∑ R ∈
                        finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                          v k,
                        ∑ i :
                          ι n v hasGhost hasOrigin hasEndpoint R,
                          rowMajorant hasGhost hasOrigin hasEndpoint R i;
                  cap *
                        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                          β H n +
                      cap *
                        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                          β H n v +
                      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                        β H n v +
                      (SourceClassEndpointMembershipResidualShellShare15.ofFourShare
                        v zero_none two_none two_endpoint two_origin two_ghost
                        two_ghost_endpoint two_ghost_origin
                        fourMajorant).total < D)

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitRowEnvelopeStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
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
            ∃ zero_none two_none two_endpoint two_origin two_ghost
                two_ghost_endpoint two_ghost_origin : ℝ,
              ∃ rowEnvelope :
                  ∀ hasGhost hasOrigin hasEndpoint
                    (R : Finset (Option (FK.boxVerts 3 n))),
                    ι n v hasGhost hasOrigin hasEndpoint R → ℝ,
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).zero_none ≤ zero_none ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_none ≤ two_none ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_endpoint ≤ two_endpoint ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_origin ≤ two_origin ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost ≤ two_ghost ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost_endpoint ≤
                  two_ghost_endpoint ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost_origin ≤ two_ghost_origin ∧
                (∀ hasGhost hasOrigin hasEndpoint k,
                  k ∈
                      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
                        v hasGhost hasOrigin hasEndpoint →
                    ∀ R,
                      R ∈
                          finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                            v k →
                        ∀ i :
                          ι n v hasGhost hasOrigin hasEndpoint R,
                          ∀ E,
                            E ∈
                                finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
                                  v Ωnz hasGhost hasOrigin hasEndpoint R
                                  (label Ωnz v hasGhost hasOrigin hasEndpoint R)
                                  i →
                              finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                                  β H E ≤
                                rowEnvelope hasGhost hasOrigin hasEndpoint R i) ∧
                (let fourMajorant : Bool → Bool → Bool → ℕ → ℝ :=
                    fun hasGhost hasOrigin hasEndpoint k =>
                      ∑ R ∈
                        finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                          v k,
                        ∑ i :
                          ι n v hasGhost hasOrigin hasEndpoint R,
                          ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
                              v Ωnz hasGhost hasOrigin hasEndpoint R
                              (label Ωnz v hasGhost hasOrigin hasEndpoint R)
                              i).card : ℝ) *
                            rowEnvelope hasGhost hasOrigin hasEndpoint R i;
                  cap *
                        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                          β H n +
                      cap *
                        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                          β H n v +
                      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                        β H n v +
                      (SourceClassEndpointMembershipResidualShellShare15.ofFourShare
                        v zero_none two_none two_endpoint two_origin two_ghost
                        two_ghost_endpoint two_ghost_origin
                        fourMajorant).total < D)

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitRowEnvelopeCardMajorantStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
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
            ∃ zero_none two_none two_endpoint two_origin two_ghost
                two_ghost_endpoint two_ghost_origin : ℝ,
              ∃ rowEnvelope cardMajorant :
                  ∀ hasGhost hasOrigin hasEndpoint
                    (R : Finset (Option (FK.boxVerts 3 n))),
                    ι n v hasGhost hasOrigin hasEndpoint R → ℝ,
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).zero_none ≤ zero_none ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_none ≤ two_none ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_endpoint ≤ two_endpoint ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_origin ≤ two_origin ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost ≤ two_ghost ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost_endpoint ≤
                  two_ghost_endpoint ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost_origin ≤ two_ghost_origin ∧
                (∀ hasGhost hasOrigin hasEndpoint k,
                  k ∈
                      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
                        v hasGhost hasOrigin hasEndpoint →
                    ∀ R,
                      R ∈
                          finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                            v k →
                        ∀ i :
                          ι n v hasGhost hasOrigin hasEndpoint R,
                          ∀ E,
                            E ∈
                                finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
                                  v Ωnz hasGhost hasOrigin hasEndpoint R
                                  (label Ωnz v hasGhost hasOrigin hasEndpoint R)
                                  i →
                              finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                                  β H E ≤
                                rowEnvelope hasGhost hasOrigin hasEndpoint R i) ∧
                (∀ hasGhost hasOrigin hasEndpoint k,
                  k ∈
                      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
                        v hasGhost hasOrigin hasEndpoint →
                    ∀ R,
                      R ∈
                          finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                            v k →
                        ∀ i :
                          ι n v hasGhost hasOrigin hasEndpoint R,
                          ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
                              v Ωnz hasGhost hasOrigin hasEndpoint R
                              (label Ωnz v hasGhost hasOrigin hasEndpoint R)
                              i).card : ℝ) ≤
                            cardMajorant hasGhost hasOrigin hasEndpoint R i) ∧
                (∀ hasGhost hasOrigin hasEndpoint k,
                  k ∈
                      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
                        v hasGhost hasOrigin hasEndpoint →
                    ∀ R,
                      R ∈
                          finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                            v k →
                        ∀ i :
                          ι n v hasGhost hasOrigin hasEndpoint R,
                          0 ≤ rowEnvelope hasGhost hasOrigin hasEndpoint R i) ∧
                (let fourMajorant : Bool → Bool → Bool → ℕ → ℝ :=
                    fun hasGhost hasOrigin hasEndpoint k =>
                      ∑ R ∈
                        finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                          v k,
                        ∑ i :
                          ι n v hasGhost hasOrigin hasEndpoint R,
                          cardMajorant hasGhost hasOrigin hasEndpoint R i *
                            rowEnvelope hasGhost hasOrigin hasEndpoint R i;
                  cap *
                        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                          β H n +
                      cap *
                        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                          β H n v +
                      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                        β H n v +
                      (SourceClassEndpointMembershipResidualShellShare15.ofFourShare
                        v zero_none two_none two_endpoint two_origin two_ghost
                        two_ghost_endpoint two_ghost_origin
                        fourMajorant).total < D)

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitRowEnvelopeClassifiedCardStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
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
            ∃ zero_none two_none two_endpoint two_origin two_ghost
                two_ghost_endpoint two_ghost_origin : ℝ,
              ∃ rowEnvelope :
                  ∀ hasGhost hasOrigin hasEndpoint
                    (R : Finset (Option (FK.boxVerts 3 n))),
                    ι n v hasGhost hasOrigin hasEndpoint R → ℝ,
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).zero_none ≤ zero_none ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_none ≤ two_none ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_endpoint ≤ two_endpoint ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_origin ≤ two_origin ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost ≤ two_ghost ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost_endpoint ≤
                  two_ghost_endpoint ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost_origin ≤ two_ghost_origin ∧
                (∀ hasGhost hasOrigin hasEndpoint k,
                  k ∈
                      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
                        v hasGhost hasOrigin hasEndpoint →
                    ∀ R,
                      R ∈
                          finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                            v k →
                        ∀ i :
                          ι n v hasGhost hasOrigin hasEndpoint R,
                          ∀ E,
                            E ∈
                                finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
                                  v Ωnz hasGhost hasOrigin hasEndpoint R
                                  (label Ωnz v hasGhost hasOrigin hasEndpoint R)
                                  i →
                              finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                                  β H E ≤
                                rowEnvelope hasGhost hasOrigin hasEndpoint R i) ∧
                (∀ hasGhost hasOrigin hasEndpoint k,
                  k ∈
                      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
                        v hasGhost hasOrigin hasEndpoint →
                    ∀ R,
                      R ∈
                          finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                            v k →
                        ∀ i :
                          ι n v hasGhost hasOrigin hasEndpoint R,
                          0 ≤ rowEnvelope hasGhost hasOrigin hasEndpoint R i) ∧
                (let fourMajorant : Bool → Bool → Bool → ℕ → ℝ :=
                    fun hasGhost hasOrigin hasEndpoint k =>
                      ∑ R ∈
                        finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                          v k,
                        ∑ i :
                          ι n v hasGhost hasOrigin hasEndpoint R,
                          ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
                              v Ωnz hasGhost hasOrigin hasEndpoint R).card :
                              ℝ) *
                            rowEnvelope hasGhost hasOrigin hasEndpoint R i;
                  cap *
                        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                          β H n +
                      cap *
                        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                          β H n v +
                      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                        β H n v +
                              (SourceClassEndpointMembershipResidualShellShare15.ofFourShare
                                v zero_none two_none two_endpoint two_origin two_ghost
                                two_ghost_endpoint two_ghost_origin
                                fourMajorant).total < D)

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitResidualEnvelopeClassifiedCardStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
    (ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*)
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    (_label :
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
            ∃ zero_none two_none two_endpoint two_origin two_ghost
                two_ghost_endpoint two_ghost_origin : ℝ,
              ∃ residualEnvelope :
                  ∀ _ _ _ (_ : Finset (Option (FK.boxVerts 3 n))), ℝ,
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).zero_none ≤ zero_none ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_none ≤ two_none ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_endpoint ≤ two_endpoint ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_origin ≤ two_origin ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost ≤ two_ghost ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost_endpoint ≤
                  two_ghost_endpoint ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost_origin ≤ two_ghost_origin ∧
                (∀ hasGhost hasOrigin hasEndpoint k,
                  k ∈
                      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
                        v hasGhost hasOrigin hasEndpoint →
                    ∀ R,
                      R ∈
                          finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                            v k →
                        ∀ E,
                          E ∈
                              finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
                                v Ωnz hasGhost hasOrigin hasEndpoint R →
                            finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                                β H E ≤
                              residualEnvelope hasGhost hasOrigin hasEndpoint R) ∧
                (let fourMajorant : Bool → Bool → Bool → ℕ → ℝ :=
                    fun hasGhost hasOrigin hasEndpoint k =>
                      ∑ R ∈
                        finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                          v k,
                        ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
                            v Ωnz hasGhost hasOrigin hasEndpoint R).card :
                            ℝ) *
                          residualEnvelope hasGhost hasOrigin hasEndpoint R;
                  cap *
                        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                          β H n +
                      cap *
                        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                          β H n v +
                      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                        β H n v +
                              (SourceClassEndpointMembershipResidualShellShare15.ofFourShare
                                v zero_none two_none two_endpoint two_origin two_ghost
                                two_ghost_endpoint two_ghost_origin
                                fourMajorant).total < D)

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitLabelFreeResidualEnvelopeClassifiedCardStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical :
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
            ∃ zero_none two_none two_endpoint two_origin two_ghost
                two_ghost_endpoint two_ghost_origin : ℝ,
              ∃ residualEnvelope :
                  ∀ _ _ _ (_ : Finset (Option (FK.boxVerts 3 n))), ℝ,
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).zero_none ≤ zero_none ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_none ≤ two_none ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_endpoint ≤ two_endpoint ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_origin ≤ two_origin ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost ≤ two_ghost ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost_endpoint ≤
                  two_ghost_endpoint ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost_origin ≤ two_ghost_origin ∧
                (∀ hasGhost hasOrigin hasEndpoint k,
                  k ∈
                      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
                        v hasGhost hasOrigin hasEndpoint →
                    ∀ R,
                      R ∈
                          finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                            v k →
                        ∀ E,
                          E ∈
                              finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
                                v Ωnz hasGhost hasOrigin hasEndpoint R →
                            finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                                β H E ≤
                              residualEnvelope hasGhost hasOrigin hasEndpoint R) ∧
                (let fourMajorant : Bool → Bool → Bool → ℕ → ℝ :=
                    fun hasGhost hasOrigin hasEndpoint k =>
                      ∑ R ∈
                        finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                          v k,
                        ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
                            v Ωnz hasGhost hasOrigin hasEndpoint R).card :
                            ℝ) *
                          residualEnvelope hasGhost hasOrigin hasEndpoint R;
                  cap *
                        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                          β H n +
                      cap *
                        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                          β H n v +
                      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                        β H n v +
                      (SourceClassEndpointMembershipResidualShellShare15.ofFourShare
                        v zero_none two_none two_endpoint two_origin two_ghost
                        two_ghost_endpoint two_ghost_origin
                        fourMajorant).total < D)

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitLabelFreePointwiseClassifiedStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical :
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
            ∃ zero_none two_none two_endpoint two_origin two_ghost
                two_ghost_endpoint two_ghost_origin : ℝ,
              ∃ pointMajorant :
                  ∀ _ _ _
                    (_ : Finset (Option (FK.boxVerts 3 n))),
                    finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
                      n v →
                      ℝ,
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).zero_none ≤ zero_none ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_none ≤ two_none ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_endpoint ≤ two_endpoint ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_origin ≤ two_origin ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost ≤ two_ghost ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost_endpoint ≤
                  two_ghost_endpoint ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost_origin ≤ two_ghost_origin ∧
                (∀ hasGhost hasOrigin hasEndpoint k,
                  k ∈
                      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
                        v hasGhost hasOrigin hasEndpoint →
                    ∀ R,
                      R ∈
                          finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                            v k →
                        ∀ E,
                          E ∈
                              finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
                                v Ωnz hasGhost hasOrigin hasEndpoint R →
                            finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                                β H E ≤
                              pointMajorant hasGhost hasOrigin hasEndpoint R E) ∧
                (let fourMajorant : Bool → Bool → Bool → ℕ → ℝ :=
                    fun hasGhost hasOrigin hasEndpoint k =>
                      ∑ R ∈
                        finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                          v k,
                        ∑ E ∈
                          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
                            v Ωnz hasGhost hasOrigin hasEndpoint R,
                          pointMajorant hasGhost hasOrigin hasEndpoint R E;
                  cap *
                        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                          β H n +
                      cap *
                        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                          β H n v +
                      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                        β H n v +
                      (SourceClassEndpointMembershipResidualShellShare15.ofFourShare
                        v zero_none two_none two_endpoint two_origin two_ghost
                        two_ghost_endpoint two_ghost_origin
                        fourMajorant).total < D)

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedResidualEnvelopeClassifiedCardExpandedStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical :
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
            ∃ zero_none two_none two_endpoint two_origin two_ghost
                two_ghost_endpoint two_ghost_origin : ℝ,
              ∃ residualEnvelope :
                  Bool → Bool → Bool →
                    Finset (Option (FK.boxVerts 3 n)) → ℝ,
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).zero_none ≤ zero_none ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_none ≤ two_none ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_endpoint ≤ two_endpoint ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_origin ≤ two_origin ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost ≤ two_ghost ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost_endpoint ≤
                  two_ghost_endpoint ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost_origin ≤ two_ghost_origin ∧
                (∀ hasGhost hasOrigin hasEndpoint k,
                  k ∈
                      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
                        v hasGhost hasOrigin hasEndpoint →
                    ∀ R,
                      R ∈
                          finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                            v k →
                        ∀ E,
                          E ∈
                              finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
                                v Ωnz hasGhost hasOrigin hasEndpoint R →
                            finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                                β H E ≤
                              residualEnvelope hasGhost hasOrigin hasEndpoint R) ∧
                cap *
                      finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                        β H n +
                    cap *
                      finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                        β H n v +
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                      β H n v +
                    SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal
                      v zero_none two_none two_endpoint two_origin two_ghost
                      two_ghost_endpoint two_ghost_origin
                      (SourceClassEndpointMembershipResidualShellShare15.residualEnvelopeClassifiedCardFourMajorant
                        v Ωnz residualEnvelope) < D

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedPointwiseClassifiedExpandedStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical :
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
            ∃ zero_none two_none two_endpoint two_origin two_ghost
                two_ghost_endpoint two_ghost_origin : ℝ,
              ∃ pointMajorant :
                  ∀ (_ : Bool) (_ : Bool) (_ : Bool)
                    (_ : Finset (Option (FK.boxVerts 3 n))),
                    finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
                      n v →
                      ℝ,
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).zero_none ≤ zero_none ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_none ≤ two_none ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_endpoint ≤ two_endpoint ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_origin ≤ two_origin ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost ≤ two_ghost ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost_endpoint ≤
                  two_ghost_endpoint ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost_origin ≤ two_ghost_origin ∧
                (∀ hasGhost hasOrigin hasEndpoint k,
                  k ∈
                      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
                        v hasGhost hasOrigin hasEndpoint →
                    ∀ R,
                      R ∈
                          finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                            v k →
                        ∀ E,
                          E ∈
                              finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
                                v Ωnz hasGhost hasOrigin hasEndpoint R →
                            finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                                β H E ≤
                              pointMajorant hasGhost hasOrigin hasEndpoint R E) ∧
                cap *
                      finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                        β H n +
                    cap *
                      finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                        β H n v +
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                      β H n v +
                    SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal
                      v zero_none two_none two_endpoint two_origin two_ghost
                      two_ghost_endpoint two_ghost_origin
                      (SourceClassEndpointMembershipResidualShellShare15.pointwiseClassifiedFourMajorant
                        v Ωnz pointMajorant) < D

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedResidualEnvelopeClassifiedCardCanonicalExpandedStrictRemainderAbsorptionPositiveSubcritical :
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
            let B :=
              finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                β H n Ωnz v
            let paid :=
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                    β H n +
                cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                    β H n v +
                finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v
            ∃ residualEnvelope :
                Bool → Bool → Bool →
                  Finset (Option (FK.boxVerts 3 n)) → ℝ,
              (∀ hasGhost hasOrigin hasEndpoint k,
                k ∈
                    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
                      v hasGhost hasOrigin hasEndpoint →
                  ∀ R,
                    R ∈
                        finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                          v k →
                      ∀ E,
                        E ∈
                            finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
                              v Ωnz hasGhost hasOrigin hasEndpoint R →
                          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                              β H E ≤
                            residualEnvelope hasGhost hasOrigin hasEndpoint R) ∧
              SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal
                  v B.zero_none B.two_none B.two_endpoint B.two_origin
                  B.two_ghost B.two_ghost_endpoint B.two_ghost_origin
                  (SourceClassEndpointMembershipResidualShellShare15.residualEnvelopeClassifiedCardFourMajorant
                    v Ωnz residualEnvelope) <
                D - paid

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedPointwiseClassifiedCanonicalExpandedStrictRemainderAbsorptionPositiveSubcritical :
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
            let B :=
              finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                β H n Ωnz v
            let paid :=
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                    β H n +
                cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                    β H n v +
                finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v
            ∃ pointMajorant :
                Bool → Bool → Bool →
                  Finset (Option (FK.boxVerts 3 n)) →
                    finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
                      n v →
                      ℝ,
              (∀ hasGhost hasOrigin hasEndpoint k,
                k ∈
                    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
                      v hasGhost hasOrigin hasEndpoint →
                  ∀ R,
                    R ∈
                        finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                          v k →
                      ∀ E,
                        E ∈
                            finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
                              v Ωnz hasGhost hasOrigin hasEndpoint R →
                          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                              β H E ≤
                            pointMajorant hasGhost hasOrigin hasEndpoint R E) ∧
              SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal
                  v B.zero_none B.two_none B.two_endpoint B.two_origin
                  B.two_ghost B.two_ghost_endpoint B.two_ghost_origin
                  (SourceClassEndpointMembershipResidualShellShare15.pointwiseClassifiedFourMajorant
                    v Ωnz pointMajorant) <
                D - paid

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitPointwiseStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
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
            ∃ zero_none two_none two_endpoint two_origin two_ghost
                two_ghost_endpoint two_ghost_origin : ℝ,
              ∃ pointMajorant :
                  ∀ hasGhost hasOrigin hasEndpoint
                    (R : Finset (Option (FK.boxVerts 3 n))),
                    ι n v hasGhost hasOrigin hasEndpoint R →
                      finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
                        n v →
                        ℝ,
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).zero_none ≤ zero_none ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_none ≤ two_none ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_endpoint ≤ two_endpoint ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_origin ≤ two_origin ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost ≤ two_ghost ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost_endpoint ≤
                  two_ghost_endpoint ∧
                (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                    β H n Ωnz v).two_ghost_origin ≤ two_ghost_origin ∧
                (∀ hasGhost hasOrigin hasEndpoint k,
                  k ∈
                      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
                        v hasGhost hasOrigin hasEndpoint →
                    ∀ R,
                      R ∈
                          finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                            v k →
                        ∀ i :
                          ι n v hasGhost hasOrigin hasEndpoint R,
                          ∀ E,
                            E ∈
                                finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
                                  v Ωnz hasGhost hasOrigin hasEndpoint R
                                  (label Ωnz v hasGhost hasOrigin hasEndpoint R)
                                  i →
                              finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                                  β H E ≤
                                pointMajorant hasGhost hasOrigin hasEndpoint R
                                  i E) ∧
                (let fourMajorant : Bool → Bool → Bool → ℕ → ℝ :=
                    fun hasGhost hasOrigin hasEndpoint k =>
                      ∑ R ∈
                        finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                          v k,
                        ∑ i :
                          ι n v hasGhost hasOrigin hasEndpoint R,
                          ∑ E ∈
                            finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
                              v Ωnz hasGhost hasOrigin hasEndpoint R
                              (label Ωnz v hasGhost hasOrigin hasEndpoint R) i,
                            pointMajorant hasGhost hasOrigin hasEndpoint R i E;
                  cap *
                        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                          β H n +
                      cap *
                        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                          β H n v +
                      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                        β H n v +
                      (SourceClassEndpointMembershipResidualShellShare15.ofFourShare
                        v zero_none two_none two_endpoint two_origin two_ghost
                        two_ghost_endpoint two_ghost_origin
                        fourMajorant).total < D)

end Exact3D
end StatMech
