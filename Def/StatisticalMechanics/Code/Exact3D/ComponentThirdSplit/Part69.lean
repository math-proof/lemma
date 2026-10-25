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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part65
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdExactCardShellBudget15ComponentShareAbsorptionPositiveSubcritical :
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
            ∃ oneShare boundaryPairShare emptyBoundaryShare : ℝ,
            ∃ shellShare :
              SourceClassEndpointMembershipResidualShellShare15 v,
              0 ≤ oneShare ∧
              0 ≤ boundaryPairShare ∧
              0 ≤ emptyBoundaryShare ∧
              shellShare.Nonneg ∧
              oneShare + boundaryPairShare + emptyBoundaryShare +
                  shellShare.total ≤ 1 ∧
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                    β H n ≤
                oneShare * D ∧
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                    β H n v ≤
                boundaryPairShare * D ∧
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v ≤
                emptyBoundaryShare * D ∧
              shellShare.FieldwiseLeMul β H Ωnz D

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardShellBudget15ComponentShareAbsorptionPositiveSubcritical :
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
            ∃ oneShare boundaryPairShare emptyBoundaryShare : ℝ,
            ∃ shellShare :
              SourceClassEndpointMembershipResidualShellShare15 v,
              0 ≤ oneShare ∧
              0 ≤ boundaryPairShare ∧
              0 ≤ emptyBoundaryShare ∧
              shellShare.Nonneg ∧
              oneShare + boundaryPairShare + emptyBoundaryShare +
                  shellShare.total ≤ 1 ∧
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                    β H n ≤
                oneShare * D ∧
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                    β H n v ≤
                boundaryPairShare * D ∧
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v ≤
                emptyBoundaryShare * D ∧
              shellShare.SupportFieldwiseLeMul β H Ωnz D

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardResidualCaseBudget15ComponentShareAbsorptionPositiveSubcritical :
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
            ∃ oneShare boundaryPairShare emptyBoundaryShare : ℝ,
            ∃ shellShare :
              SourceClassEndpointMembershipResidualShellShare15 v,
              0 ≤ oneShare ∧
              0 ≤ boundaryPairShare ∧
              0 ≤ emptyBoundaryShare ∧
              shellShare.Nonneg ∧
              oneShare + boundaryPairShare + emptyBoundaryShare +
                  shellShare.total ≤ 1 ∧
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                    β H n ≤
                oneShare * D ∧
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                    β H n v ≤
                boundaryPairShare * D ∧
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v ≤
                emptyBoundaryShare * D ∧
              shellShare.SupportResidualCaseFieldwiseLeMul β H Ωnz D

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardDependentLabelBudget15ComponentShareAbsorptionPositiveSubcritical
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
            ∃ oneShare boundaryPairShare emptyBoundaryShare : ℝ,
            ∃ shellShare :
              SourceClassEndpointMembershipResidualShellShare15 v,
              0 ≤ oneShare ∧
              0 ≤ boundaryPairShare ∧
              0 ≤ emptyBoundaryShare ∧
              shellShare.Nonneg ∧
              oneShare + boundaryPairShare + emptyBoundaryShare +
                  shellShare.total ≤ 1 ∧
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                    β H n ≤
                oneShare * D ∧
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                    β H n v ≤
                boundaryPairShare * D ∧
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v ≤
                emptyBoundaryShare * D ∧
              shellShare.SupportResidualCaseDependentLabelFieldwiseLeMul
                β H Ωnz D (ι n v) (label Ωnz v)

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardPointwiseDependentLabelBudget15ComponentShareAbsorptionPositiveSubcritical
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
            ∃ oneShare boundaryPairShare emptyBoundaryShare : ℝ,
            ∃ shellShare :
              SourceClassEndpointMembershipResidualShellShare15 v,
              0 ≤ oneShare ∧
              0 ≤ boundaryPairShare ∧
              0 ≤ emptyBoundaryShare ∧
              shellShare.Nonneg ∧
              oneShare + boundaryPairShare + emptyBoundaryShare +
                  shellShare.total ≤ 1 ∧
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                    β H n ≤
                oneShare * D ∧
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                    β H n v ≤
                boundaryPairShare * D ∧
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v ≤
                emptyBoundaryShare * D ∧
              shellShare.SupportResidualCasePointwiseDependentLabelFieldwiseLeMul
                β H Ωnz D (ι n v) (label Ωnz v)

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardNormalizedRowDependentLabelBudget15ComponentShareAbsorptionPositiveSubcritical
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
            ∃ oneShare boundaryPairShare emptyBoundaryShare : ℝ,
            ∃ shellShare :
              SourceClassEndpointMembershipResidualShellShare15 v,
              0 < D ∧
              0 ≤ oneShare ∧
              0 ≤ boundaryPairShare ∧
              0 ≤ emptyBoundaryShare ∧
              shellShare.Nonneg ∧
              oneShare + boundaryPairShare + emptyBoundaryShare +
                  shellShare.total ≤ 1 ∧
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                    β H n ≤
                oneShare * D ∧
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                    β H n v ≤
                boundaryPairShare * D ∧
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v ≤
                emptyBoundaryShare * D ∧
              (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                β H n Ωnz v).zero_none ≤ shellShare.zero_none * D ∧
              (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                β H n Ωnz v).two_none ≤ shellShare.two_none * D ∧
              (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                β H n Ωnz v).two_endpoint ≤ shellShare.two_endpoint * D ∧
              (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                β H n Ωnz v).two_origin ≤ shellShare.two_origin * D ∧
              (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                β H n Ωnz v).two_ghost ≤ shellShare.two_ghost * D ∧
              (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                β H n Ωnz v).two_ghost_endpoint ≤
                  shellShare.two_ghost_endpoint * D ∧
              (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                β H n Ωnz v).two_ghost_origin ≤
                  shellShare.two_ghost_origin * D ∧
              ∀ hasGhost hasOrigin hasEndpoint k,
                k ∈
                    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
                      v hasGhost hasOrigin hasEndpoint →
                  shellShare.fourShare hasGhost hasOrigin hasEndpoint k =
                    ∑ R ∈
                      finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                        v k,
                      ∑ i : ι n v hasGhost hasOrigin hasEndpoint R,
                        ∑ E ∈
                          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
                            v Ωnz hasGhost hasOrigin hasEndpoint R
                            (label Ωnz v hasGhost hasOrigin hasEndpoint R) i,
                          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                            β H E / D

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15ComponentShareAbsorptionPositiveSubcritical
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
            let shellShare :=
              SourceClassEndpointMembershipResidualShellShare15.normalizedRows
                v β H D Ωnz (ι n v) (label Ωnz v)
            0 < D ∧
              cap *
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                      β H n / D +
                  cap *
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                      β H n v / D +
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                    β H n v / D +
                  shellShare.total ≤ 1

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15ComponentSumAbsorptionPositiveSubcritical
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
            let shellShare :=
              SourceClassEndpointMembershipResidualShellShare15.normalizedRows
                v β H D Ωnz (ι n v) (label Ωnz v)
            0 < D ∧
              cap *
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                      β H n +
                  cap *
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                      β H n v +
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                    β H n v +
                  shellShare.total * D ≤ D

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentSumAbsorptionPositiveSubcritical
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
            let rawShell :=
              SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawTotal
                v β H Ωnz (ι n v) (label Ωnz v)
            0 < D ∧
              cap *
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                      β H n +
                  cap *
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                      β H n v +
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                    β H n v +
                  rawShell ≤ D

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical
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
            let rawShell :=
              SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawTotal
                v β H Ωnz (ι n v) (label Ωnz v)
            cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                    β H n +
                cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                    β H n v +
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                    β H n v +
                rawShell ≤ D

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderDenominatorFreeAbsorptionPositiveSubcritical
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
            let rawShell :=
              SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawTotal
                v β H Ωnz (ι n v) (label Ωnz v)
            let paid :=
              cap *
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                      β H n +
                  cap *
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                      β H n v +
                finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v
            rawShell ≤ D - paid

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorptionPositiveSubcritical
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
            let rawShell :=
              SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawTotal
                v β H Ωnz (ι n v) (label Ωnz v)
            cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                    β H n +
                cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                    β H n v +
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                    β H n v +
                rawShell < D

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorptionPositiveSubcritical :
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
            let rawShell :=
              SourceClassEndpointMembershipResidualShellShare15.labelFreeRawTotal
                v β H Ωnz
            cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                    β H n +
                cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                    β H n v +
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                    β H n v +
                rawShell < D

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical :
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
              SourceClassEndpointMembershipResidualShellShare15.labelFreeRawBudget15
                v β H Ωnz
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


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical :
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
              shellMajorant.LabelFreeRawFieldwiseLe β H Ωnz ∧
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


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExplicitStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical :
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
                    SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
                      v β H Ωnz hasGhost hasOrigin hasEndpoint k ≤
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


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExpandedStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical :
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
                    SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
                      v β H Ωnz hasGhost hasOrigin hasEndpoint k ≤
                      fourMajorant hasGhost hasOrigin hasEndpoint k) ∧
                cap *
                      finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                        β H n +
                    cap *
                      finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                        β H n v +
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                      β H n v +
                    (zero_none +
                      two_none +
                      two_endpoint +
                      two_origin +
                      two_ghost +
                      two_ghost_endpoint +
                      two_ghost_origin +
                      (∑ k ∈
                        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
                          v false false false,
                        fourMajorant false false false k) +
                      (∑ k ∈
                        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
                          v false false true,
                        fourMajorant false false true k) +
                      (∑ k ∈
                        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
                          v false true false,
                        fourMajorant false true false k) +
                      (∑ k ∈
                        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
                          v false true true,
                        fourMajorant false true true k) +
                      (∑ k ∈
                        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
                          v true false false,
                        fourMajorant true false false k) +
                      (∑ k ∈
                        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
                          v true false true,
                        fourMajorant true false true k) +
                      (∑ k ∈
                        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
                          v true true false,
                        fourMajorant true true false k) +
                      (∑ k ∈
                        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
                        v true true true,
                        fourMajorant true true true k)) < D

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellIccExactCardImageExpandedStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical :
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
                      Finset.Icc
                        (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
                          hasGhost hasOrigin hasEndpoint)
                        ((2 * n + 1) ^ 3 - 2) →
                    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
                      β H n Ωnz v hasGhost hasOrigin hasEndpoint k ≤
                      fourMajorant hasGhost hasOrigin hasEndpoint k) ∧
                cap *
                      finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                        β H n +
                    cap *
                      finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                        β H n v +
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                      β H n v +
                    (zero_none +
                      two_none +
                      two_endpoint +
                      two_origin +
                      two_ghost +
                      two_ghost_endpoint +
                      two_ghost_origin +
                      (∑ k ∈
                        Finset.Icc
                          (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
                            false false false)
                          ((2 * n + 1) ^ 3 - 2),
                        fourMajorant false false false k) +
                      (∑ k ∈
                        Finset.Icc
                          (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
                            false false true)
                          ((2 * n + 1) ^ 3 - 2),
                        fourMajorant false false true k) +
                      (∑ k ∈
                        Finset.Icc
                          (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
                            false true false)
                          ((2 * n + 1) ^ 3 - 2),
                        fourMajorant false true false k) +
                      (∑ k ∈
                        Finset.Icc
                          (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
                            false true true)
                          ((2 * n + 1) ^ 3 - 2),
                        fourMajorant false true true k) +
                      (∑ k ∈
                        Finset.Icc
                          (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
                            true false false)
                          ((2 * n + 1) ^ 3 - 2),
                        fourMajorant true false false k) +
                      (∑ k ∈
                        Finset.Icc
                          (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
                            true false true)
                          ((2 * n + 1) ^ 3 - 2),
                        fourMajorant true false true k) +
                      (∑ k ∈
                        Finset.Icc
                          (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
                            true true false)
                          ((2 * n + 1) ^ 3 - 2),
                        fourMajorant true true false k) +
                      (∑ k ∈
                        Finset.Icc
                          (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
                            true true true)
                          ((2 * n + 1) ^ 3 - 2),
                        fourMajorant true true true k)) < D

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageExpandedStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical :
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
                (∀ k, k ∈ Finset.Icc 4 ((2 * n + 1) ^ 3 - 2) →
                  finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
                    β H n Ωnz v false false false k ≤
                    fourMajorant false false false k) ∧
                (∀ k, k ∈ Finset.Icc 3 ((2 * n + 1) ^ 3 - 2) →
                  finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
                    β H n Ωnz v false false true k ≤
                    fourMajorant false false true k) ∧
                (∀ k, k ∈ Finset.Icc 3 ((2 * n + 1) ^ 3 - 2) →
                  finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
                    β H n Ωnz v false true false k ≤
                    fourMajorant false true false k) ∧
                (∀ k, k ∈ Finset.Icc 2 ((2 * n + 1) ^ 3 - 2) →
                  finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
                    β H n Ωnz v false true true k ≤
                    fourMajorant false true true k) ∧
                (∀ k, k ∈ Finset.Icc 3 ((2 * n + 1) ^ 3 - 2) →
                  finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
                    β H n Ωnz v true false false k ≤
                    fourMajorant true false false k) ∧
                (∀ k, k ∈ Finset.Icc 2 ((2 * n + 1) ^ 3 - 2) →
                  finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
                    β H n Ωnz v true false true k ≤
                    fourMajorant true false true k) ∧
                (∀ k, k ∈ Finset.Icc 2 ((2 * n + 1) ^ 3 - 2) →
                  finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
                    β H n Ωnz v true true false k ≤
                    fourMajorant true true false k) ∧
                (∀ k, k ∈ Finset.Icc 1 ((2 * n + 1) ^ 3 - 2) →
                  finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
                    β H n Ωnz v true true true k ≤
                    fourMajorant true true true k) ∧
                cap *
                      finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                        β H n +
                    cap *
                      finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                        β H n v +
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                      β H n v +
                    (zero_none +
                      two_none +
                      two_endpoint +
                      two_origin +
                      two_ghost +
                      two_ghost_endpoint +
                      two_ghost_origin +
                      (∑ k ∈ Finset.Icc 4 ((2 * n + 1) ^ 3 - 2),
                        fourMajorant false false false k) +
                      (∑ k ∈ Finset.Icc 3 ((2 * n + 1) ^ 3 - 2),
                        fourMajorant false false true k) +
                      (∑ k ∈ Finset.Icc 3 ((2 * n + 1) ^ 3 - 2),
                        fourMajorant false true false k) +
                      (∑ k ∈ Finset.Icc 2 ((2 * n + 1) ^ 3 - 2),
                        fourMajorant false true true k) +
                      (∑ k ∈ Finset.Icc 3 ((2 * n + 1) ^ 3 - 2),
                        fourMajorant true false false k) +
                      (∑ k ∈ Finset.Icc 2 ((2 * n + 1) ^ 3 - 2),
                        fourMajorant true false true k) +
                      (∑ k ∈ Finset.Icc 2 ((2 * n + 1) ^ 3 - 2),
                        fourMajorant true true false k) +
                      (∑ k ∈ Finset.Icc 1 ((2 * n + 1) ^ 3 - 2),
                        fourMajorant true true true k)) < D

set_option linter.style.longLine false in


noncomputable def finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointContribution
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) : ℝ :=
  ∑ k ∈ Finset.Icc 1 ((2 * n + 1) ^ 3 - 2),
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
      β H n Ω v true true true k

end Exact3D
end StatMech
