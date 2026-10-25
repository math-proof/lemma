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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part117
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellMajorantDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSum
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellMajorantDenominatorFreeAbsorptionPositiveSubcritical
        ι label := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let shellMajorant :=
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawShell
      v β H Ωnz (ι n v) (label Ωnz v)
  let rawShell :=
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawTotal
      v β H Ωnz (ι n v) (label Ωnz v)
  refine ⟨shellMajorant, ?_, ?_⟩
  · exact
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawShell_rawFieldwiseLe
        (v := v) (β := β) (H := H) (Ω := Ωnz)
        (ι := ι n v) (label := label Ωnz v)
  · have htotal : shellMajorant.total = rawShell := by
      simpa [shellMajorant, rawShell] using
        SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawShell_total
          (v := v) (β := β) (H := H) (Ω := Ωnz)
          (ι := ι n v) (label := label Ωnz v)
    calc
      cap *
              finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                β H n +
            cap *
              finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                β H n v +
            finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
              β H n v +
            shellMajorant.total =
          cap *
              finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                β H n +
            cap *
              finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                β H n v +
            finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
              β H n v +
            rawShell := by
        rw [htotal]
      _ ≤ D := by
        simpa [rawShell, cap, D, Ωnz] using hn H hH Ω v hv

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellMajorantShareAbsorption_of_boundaryCrossingRemainderPositive_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellMajorantDenominatorFree
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (hpos :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
    (hmajorant :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellMajorantDenominatorFreeAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellMajorantShareAbsorptionPositiveSubcritical
        ι label := by
  intro β hβpos hβc
  filter_upwards [hpos β hβpos hβc, hmajorant β hβpos hβc] with
    n hnpos hnmajorant
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let paid :=
    cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n +
      cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
          β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
        β H n v
  let R := D - paid
  rcases hnmajorant H hH Ω v hv with
    ⟨shellMajorant, hrawField, hdenom⟩
  have hRpos : 0 < R := by
    simpa [R, paid, Ωnz, cap, D] using hnpos H hH Ω v hv
  have htotal : shellMajorant.total ≤ R := by
    have hdenom' : paid + shellMajorant.total ≤ D := by
      simpa [paid, Ωnz, cap, D] using hdenom
    dsimp [R]
    linarith
  exact ⟨shellMajorant, hRpos, hrawField, htotal⟩

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderMajorantShareAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellMajorantShare
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellMajorantShareAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderMajorantShareAbsorptionPositiveSubcritical
        ι label := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
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
  rcases hn H hH Ω v hv with
    ⟨shellMajorant, hRpos, hrawField, htotal⟩
  refine ⟨shellMajorant.toBudget15, hRpos, ?_, ?_⟩
  · exact
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15_fieldwiseLe_toBudget15_of_rawFieldwiseLe
        (Sh := shellMajorant) (β := β) (H := H) (Ω := Ωnz)
        (ι := ι n v) (label := label Ωnz v) hrawField
  · simpa [SourceClassEndpointMembershipResidualShellShare15.toBudget15_total]
      using htotal

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderMajorantShare
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderMajorantShareAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical
        ι label := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
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
  let rawShell :=
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawTotal
      v β H Ωnz (ι n v) (label Ωnz v)
  rcases hn H hH Ω v hv with ⟨B, hRpos, hfield, hsum⟩
  have hrawLe : rawShell ≤ B.total := by
    calc
      rawShell = rawBudget.total := by
        symm
        simpa [rawBudget, rawShell] using
          SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15_total
            (v := v) (β := β) (H := H) (Ω := Ωnz)
            (ι := ι n v) (label := label Ωnz v)
      _ ≤ B.total :=
        SourceClassEndpointMembershipLiveBudget15.total_le_of_fieldwiseLe
          hfield
  exact ⟨hRpos, le_trans hrawLe hsum⟩

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorption_of_boundaryCrossingRemainderPositive_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellMajorantDenominatorFree
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (hpos :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
    (hmajorant :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellMajorantDenominatorFreeAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical
        ι label :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderMajorantShare
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderMajorantShareAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellMajorantShare
      (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellMajorantShareAbsorption_of_boundaryCrossingRemainderPositive_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellMajorantDenominatorFree
        hpos hmajorant))

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorption_of_boundaryCrossingRemainderPositive_canonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSum
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (hpos :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
    (hraw :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical
        ι label :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorption_of_boundaryCrossingRemainderPositive_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellMajorantDenominatorFree
    hpos
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellMajorantDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSum
      hraw)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorption_of_boundaryCrossingCapComponentStrictSum_canonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSum
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (hstrict :
      BoundaryCrossingCapComponentStrictSumPositiveSubcritical)
    (hraw :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical
        ι label :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorption_of_boundaryCrossingRemainderPositive_canonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSum
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositive_of_boundaryCrossingCapComponentStrictSum
      hstrict)
    hraw

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorption_of_boundaryCrossingCapComponentStrictShare_canonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSum
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (hstrictShare :
      BoundaryCrossingCapComponentStrictSharePositiveSubcritical)
    (hraw :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical
        ι label :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorption_of_boundaryCrossingCapComponentStrictSum_canonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSum
    (boundaryCrossingCapComponentStrictSumAbsorption_of_componentStrictShare
      hstrictShare)
    hraw

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorption_of_boundaryCrossingCapComponentStrictCanonicalRatioShareSum_canonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSum
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (hstrict :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hraw :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical
        ι label :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorption_of_boundaryCrossingCapComponentStrictShare_canonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSum
    (boundaryCrossingCapComponentStrictShareAbsorption_of_canonicalRatioShareSum
      hstrict)
    hraw

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorption_of_boundaryCrossingCapComponentStrictCanonicalRatioShareSum_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderDenominatorFree
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (hstrict :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hraw :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderDenominatorFreeAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical
        ι label :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorption_of_boundaryCrossingRemainderPositive_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositive_of_boundaryCrossingCapComponentStrictCanonicalRatioShareSum
      hstrict)
    hraw

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorption_of_boundaryCrossingCapComponentStrictCanonicalRatioShareSum_canonicalRawRowDependentLabelBudget15CanonicalRatioShareSum
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (hstrict :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hrawRatio :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15CanonicalRatioShareSumPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical
        ι label :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorption_of_boundaryCrossingCapComponentStrictCanonicalRatioShareSum_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderDenominatorFree
    hstrict
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15CanonicalRatioShareSum
      hrawRatio)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositive_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShare
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
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
  exact (by
    rcases hn H hH Ω v hv with ⟨hRpos, _hraw⟩
    simpa [R, Ωnz, cap, D] using hRpos)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShare
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical
        ι label := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
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
  let shellShare :=
    SourceClassEndpointMembershipResidualShellShare15.normalizedRows
      v β H R Ωnz (ι n v) (label Ωnz v)
  let rawShell :=
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawTotal
      v β H Ωnz (ι n v) (label Ωnz v)
  rcases hn H hH Ω v hv with ⟨hRpos, hraw⟩
  refine ⟨hRpos, ?_⟩
  have htotal : shellShare.total * R = rawShell := by
    simpa [shellShare, rawShell] using
      SourceClassEndpointMembershipResidualShellShare15.normalizedRows_total_mul_eq_rawTotal
        (v := v) (β := β) (H := H) (D := R) (Ω := Ωnz)
        (ι := ι n v) (label := label Ωnz v) hRpos.ne'
  have hshareEq : shellShare.total = rawShell / R := by
    rw [← htotal]
    exact (mul_div_cancel_right₀ shellShare.total hRpos.ne').symm
  have hdiv : rawShell / R ≤ R / R :=
    div_le_div_of_nonneg_right hraw (le_of_lt hRpos)
  calc
    shellShare.total = rawShell / R := hshareEq
    _ ≤ R / R := hdiv
    _ = 1 := by
      exact div_self hRpos.ne'

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorption_of_canonicalNormalizedRowDependentLabelBudget15BoundaryCrossingRemainderShare
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical
        ι label := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
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
  let shellShare :=
    SourceClassEndpointMembershipResidualShellShare15.normalizedRows
      v β H R Ωnz (ι n v) (label Ωnz v)
  let rawShell :=
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawTotal
      v β H Ωnz (ι n v) (label Ωnz v)
  rcases hn H hH Ω v hv with ⟨hRpos, hshare⟩
  refine ⟨hRpos, ?_⟩
  have htotal : shellShare.total * R = rawShell := by
    simpa [shellShare, rawShell] using
      SourceClassEndpointMembershipResidualShellShare15.normalizedRows_total_mul_eq_rawTotal
        (v := v) (β := β) (H := H) (D := R) (Ω := Ωnz)
        (ι := ι n v) (label := label Ωnz v) hRpos.ne'
  have hmul : shellShare.total * R ≤ 1 * R :=
    mul_le_mul_of_nonneg_right hshare (le_of_lt hRpos)
  calc
    rawShell = shellShare.total * R := htotal.symm
    _ ≤ 1 * R := hmul
    _ = R := by ring

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorption_iff_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShare
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R} :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical
        ι label ↔
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical
        ι label :=
  ⟨boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorption_of_canonicalNormalizedRowDependentLabelBudget15BoundaryCrossingRemainderShare,
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShare⟩

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictShare
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical
        ι label := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
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
  let shellShare :=
    SourceClassEndpointMembershipResidualShellShare15.normalizedRows
      v β H R Ωnz (ι n v) (label Ωnz v)
  let rawShell :=
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawTotal
      v β H Ωnz (ι n v) (label Ωnz v)
  rcases hn H hH Ω v hv with ⟨hRpos, hraw⟩
  refine ⟨hRpos, ?_⟩
  have htotal : shellShare.total * R = rawShell := by
    simpa [shellShare, rawShell] using
      SourceClassEndpointMembershipResidualShellShare15.normalizedRows_total_mul_eq_rawTotal
        (v := v) (β := β) (H := H) (D := R) (Ω := Ωnz)
        (ι := ι n v) (label := label Ωnz v) hRpos.ne'
  have hmul : shellShare.total * R < 1 * R := by
    calc
      shellShare.total * R = rawShell := htotal
      _ < R := hraw
      _ = 1 * R := by ring
  exact lt_of_mul_lt_mul_right hmul (le_of_lt hRpos)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_canonicalNormalizedRowDependentLabelBudget15BoundaryCrossingRemainderStrictShare
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical
        ι label := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
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
  let shellShare :=
    SourceClassEndpointMembershipResidualShellShare15.normalizedRows
      v β H R Ωnz (ι n v) (label Ωnz v)
  let rawShell :=
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawTotal
      v β H Ωnz (ι n v) (label Ωnz v)
  rcases hn H hH Ω v hv with ⟨hRpos, hshare⟩
  refine ⟨hRpos, ?_⟩
  have htotal : shellShare.total * R = rawShell := by
    simpa [shellShare, rawShell] using
      SourceClassEndpointMembershipResidualShellShare15.normalizedRows_total_mul_eq_rawTotal
        (v := v) (β := β) (H := H) (D := R) (Ω := Ωnz)
        (ι := ι n v) (label := label Ωnz v) hRpos.ne'
  have hmul : shellShare.total * R < 1 * R :=
    mul_lt_mul_of_pos_right hshare hRpos
  calc
    rawShell = shellShare.total * R := htotal.symm
    _ < 1 * R := hmul
    _ = R := by ring

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorption_iff_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictShare
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R} :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical
        ι label ↔
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical
        ι label :=
  ⟨boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_canonicalNormalizedRowDependentLabelBudget15BoundaryCrossingRemainderStrictShare,
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictShare⟩

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositive_of_canonicalNormalizedRowDependentLabelBudget15BoundaryCrossingRemainderStrictShare
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
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
  rcases hn H hH Ω v hv with ⟨hRpos, _hshare⟩
  simpa [R, Ωnz, cap, D] using hRpos

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositive_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictShare
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositive_of_canonicalNormalizedRowDependentLabelBudget15BoundaryCrossingRemainderStrictShare
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictShare
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardPointwiseDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_canonicalNormalizedRowDependentLabelBudget15BoundaryCrossingRemainderStrictShare
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardPointwiseDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical
        ι label := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
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
  let shellShare :=
    SourceClassEndpointMembershipResidualShellShare15.normalizedRows
      v β H R Ωnz (ι n v) (label Ωnz v)
  rcases hn H hH Ω v hv with ⟨hRpos, hshareStrict⟩
  refine ⟨shellShare, ?_, hshareStrict, ?_⟩
  · exact
      SourceClassEndpointMembershipResidualShellShare15.normalizedRows_nonneg
        (v := v) (β := β) (H := H) (D := R) (Ω := Ωnz)
        (ι := ι n v) (label := label Ωnz v)
        (le_of_lt hβpos) (le_of_lt hH) hRpos
  · refine
      SourceClassEndpointMembershipResidualShellShare15.supportResidualCasePointwiseDependentLabelFieldwiseLeMul_of_normalizedRows
        (Sh := shellShare) (β := β) (H := H) (D := R)
        (Ω := Ωnz) (ι := ι n v) (label := label Ωnz v)
        (le_of_lt hβpos) (le_of_lt hH) hRpos
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · dsimp [shellShare, SourceClassEndpointMembershipResidualShellShare15.normalizedRows]
      rw [div_mul_cancel₀ _ hRpos.ne']
    · dsimp [shellShare, SourceClassEndpointMembershipResidualShellShare15.normalizedRows]
      rw [div_mul_cancel₀ _ hRpos.ne']
    · dsimp [shellShare, SourceClassEndpointMembershipResidualShellShare15.normalizedRows]
      rw [div_mul_cancel₀ _ hRpos.ne']
    · dsimp [shellShare, SourceClassEndpointMembershipResidualShellShare15.normalizedRows]
      rw [div_mul_cancel₀ _ hRpos.ne']
    · dsimp [shellShare, SourceClassEndpointMembershipResidualShellShare15.normalizedRows]
      rw [div_mul_cancel₀ _ hRpos.ne']
    · dsimp [shellShare, SourceClassEndpointMembershipResidualShellShare15.normalizedRows]
      rw [div_mul_cancel₀ _ hRpos.ne']
    · dsimp [shellShare, SourceClassEndpointMembershipResidualShellShare15.normalizedRows]
      rw [div_mul_cancel₀ _ hRpos.ne']
    · intro hasGhost hasOrigin hasEndpoint k hk
      exact
        SourceClassEndpointMembershipResidualShellShare15.normalizedRows_fourShare
          (v := v) (β := β) (H := H) (D := R) (Ω := Ωnz)
          (ι := ι n v) (label := label Ωnz v)
          hasGhost hasOrigin hasEndpoint k

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardPointwiseDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictShare
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardPointwiseDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical
        ι label :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardPointwiseDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_canonicalNormalizedRowDependentLabelBudget15BoundaryCrossingRemainderStrictShare
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictShare
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardDependentLabelBudget15BoundaryCrossingRemainderShareAbsorption_of_canonicalNormalizedRowDependentLabelBudget15BoundaryCrossingRemainderShare
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardDependentLabelBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical
        ι label := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
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
  let shellShare :=
    SourceClassEndpointMembershipResidualShellShare15.normalizedRows
      v β H R Ωnz (ι n v) (label Ωnz v)
  rcases hn H hH Ω v hv with ⟨hRpos, hshareSum⟩
  refine
    ⟨shellShare, ?_, hshareSum, ?_⟩
  · exact
      SourceClassEndpointMembershipResidualShellShare15.normalizedRows_nonneg
        (v := v) (β := β) (H := H) (D := R) (Ω := Ωnz)
        (ι := ι n v) (label := label Ωnz v)
        (le_of_lt hβpos) (le_of_lt hH) hRpos
  · have hpointwise :
        shellShare.SupportResidualCasePointwiseDependentLabelFieldwiseLeMul
          β H Ωnz R (ι n v) (label Ωnz v) := by
      refine
        SourceClassEndpointMembershipResidualShellShare15.supportResidualCasePointwiseDependentLabelFieldwiseLeMul_of_normalizedRows
          (Sh := shellShare) (β := β) (H := H) (D := R)
          (Ω := Ωnz) (ι := ι n v) (label := label Ωnz v)
          (le_of_lt hβpos) (le_of_lt hH) hRpos
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · dsimp [shellShare, SourceClassEndpointMembershipResidualShellShare15.normalizedRows]
        rw [div_mul_cancel₀ _ hRpos.ne']
      · dsimp [shellShare, SourceClassEndpointMembershipResidualShellShare15.normalizedRows]
        rw [div_mul_cancel₀ _ hRpos.ne']
      · dsimp [shellShare, SourceClassEndpointMembershipResidualShellShare15.normalizedRows]
        rw [div_mul_cancel₀ _ hRpos.ne']
      · dsimp [shellShare, SourceClassEndpointMembershipResidualShellShare15.normalizedRows]
        rw [div_mul_cancel₀ _ hRpos.ne']
      · dsimp [shellShare, SourceClassEndpointMembershipResidualShellShare15.normalizedRows]
        rw [div_mul_cancel₀ _ hRpos.ne']
      · dsimp [shellShare, SourceClassEndpointMembershipResidualShellShare15.normalizedRows]
        rw [div_mul_cancel₀ _ hRpos.ne']
      · dsimp [shellShare, SourceClassEndpointMembershipResidualShellShare15.normalizedRows]
        rw [div_mul_cancel₀ _ hRpos.ne']
      · intro hasGhost hasOrigin hasEndpoint k hk
        exact
          SourceClassEndpointMembershipResidualShellShare15.normalizedRows_fourShare
            (v := v) (β := β) (H := H) (D := R) (Ω := Ωnz)
            (ι := ι n v) (label := label Ωnz v)
            hasGhost hasOrigin hasEndpoint k
    exact
      SourceClassEndpointMembershipResidualShellShare15.supportResidualCaseDependentLabelFieldwiseLeMul_of_pointwiseDependentLabelFieldwiseLeMul
        (Sh := shellShare) (β := β) (H := H) (Ω := Ωnz)
        (D := R) (ι := ι n v) (label := label Ωnz v)
        hpointwise

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardResidualCaseBudget15BoundaryCrossingRemainderShareAbsorption_of_dependentLabelBudget15BoundaryCrossingRemainderShare
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardDependentLabelBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardResidualCaseBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  rcases hn H hH Ω v hv with
    ⟨shellShare, hshellNonneg, hshareSum, hdependentCases⟩
  refine ⟨shellShare, hshellNonneg, hshareSum, ?_⟩
  exact
    SourceClassEndpointMembershipResidualShellShare15.supportResidualCaseFieldwiseLeMul_of_dependentLabelFieldwiseLeMul
      (Sh := shellShare) (β := β) (H := H)
      (Ω := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω)
      (D :=
        finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v -
          (boundaryCrossingCap n (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω) *
              finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                β H n +
            boundaryCrossingCap n (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω) *
              finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                β H n v +
            finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
              β H n v))
      (ι := ι n v)
      (label := label (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω) v)
      hdependentCases

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardShellBudget15BoundaryCrossingRemainderShareAbsorption_of_residualThresholdSupportExactCardResidualCaseBudget15BoundaryCrossingRemainderShare
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardResidualCaseBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardShellBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  rcases hn H hH Ω v hv with
    ⟨shellShare, hshellNonneg, hshareSum, hresidualCases⟩
  refine ⟨shellShare, hshellNonneg, hshareSum, ?_⟩
  exact
    SourceClassEndpointMembershipResidualShellShare15.supportFieldwiseLeMul_of_residualCaseFieldwiseLeMul
      hv hresidualCases

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardShellBudget15BoundaryCrossingRemainderShareAbsorption_of_dependentLabelBudget15BoundaryCrossingRemainderShare
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardDependentLabelBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardShellBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardShellBudget15BoundaryCrossingRemainderShareAbsorption_of_residualThresholdSupportExactCardResidualCaseBudget15BoundaryCrossingRemainderShare
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardResidualCaseBudget15BoundaryCrossingRemainderShareAbsorption_of_dependentLabelBudget15BoundaryCrossingRemainderShare
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdExactCardShellBudget15BoundaryCrossingRemainderShareAbsorption_of_residualThresholdSupportExactCardShellBudget15BoundaryCrossingRemainderShare
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardShellBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdExactCardShellBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  rcases hn H hH Ω v hv with
    ⟨shellShare, hshellNonneg, hshareSum, hsupportShell⟩
  refine ⟨shellShare, hshellNonneg, hshareSum, ?_⟩
  exact
    SourceClassEndpointMembershipResidualShellShare15.fieldwiseLeMul_of_supportFieldwiseLeMul
      hv hsupportShell

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareAbsorption_of_residualThresholdExactCardShellBudget15BoundaryCrossingRemainderShare
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdExactCardShellBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  rcases hn H hH Ω v hv with
    ⟨shellShare, hshellNonneg, hshareSum, hshell⟩
  refine ⟨shellShare.toBudget15, ?_, ?_, ?_⟩
  · exact
      SourceClassEndpointMembershipResidualShellShare15.toBudget15_nonneg
        hshellNonneg
  · simpa [SourceClassEndpointMembershipResidualShellShare15.toBudget15_total]
      using hshareSum
  · exact
      SourceClassEndpointMembershipResidualShellShare15.toBudget15_fieldwiseLeMul
        hshell

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareAbsorption_of_residualThresholdSupportExactCardShellBudget15BoundaryCrossingRemainderShare
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardShellBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareAbsorption_of_residualThresholdExactCardShellBudget15BoundaryCrossingRemainderShare
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdExactCardShellBudget15BoundaryCrossingRemainderShareAbsorption_of_residualThresholdSupportExactCardShellBudget15BoundaryCrossingRemainderShare
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardResidualCaseBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_dependentLabelBudget15BoundaryCrossingRemainderStrictShare
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardResidualCaseBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  rcases hn H hH Ω v hv with
    ⟨shellShare, hshellNonneg, hshareSum, hdependentCases⟩
  refine ⟨shellShare, hshellNonneg, hshareSum, ?_⟩
  exact
    SourceClassEndpointMembershipResidualShellShare15.supportResidualCaseFieldwiseLeMul_of_dependentLabelFieldwiseLeMul
      (Sh := shellShare) (β := β) (H := H)
      (Ω := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω)
      (D :=
        finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v -
          (boundaryCrossingCap n (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω) *
              finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                β H n +
            boundaryCrossingCap n (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω) *
              finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                β H n v +
            finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
              β H n v))
      (ι := ι n v)
      (label := label (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω) v)
      hdependentCases

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardShellBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_residualThresholdSupportExactCardResidualCaseBudget15BoundaryCrossingRemainderStrictShare
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardResidualCaseBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardShellBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  rcases hn H hH Ω v hv with
    ⟨shellShare, hshellNonneg, hshareSum, hresidualCases⟩
  refine ⟨shellShare, hshellNonneg, hshareSum, ?_⟩
  exact
    SourceClassEndpointMembershipResidualShellShare15.supportFieldwiseLeMul_of_residualCaseFieldwiseLeMul
      hv hresidualCases

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardShellBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_dependentLabelBudget15BoundaryCrossingRemainderStrictShare
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardShellBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardShellBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_residualThresholdSupportExactCardResidualCaseBudget15BoundaryCrossingRemainderStrictShare
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardResidualCaseBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_dependentLabelBudget15BoundaryCrossingRemainderStrictShare
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_pointwiseDependentLabelBudget15BoundaryCrossingRemainderStrictShare
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardPointwiseDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical
        ι label := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  rcases hn H hH Ω v hv with
    ⟨shellShare, hshellNonneg, hshareStrict, hpointwiseCases⟩
  refine ⟨shellShare, hshellNonneg, hshareStrict, ?_⟩
  exact
    SourceClassEndpointMembershipResidualShellShare15.supportResidualCaseDependentLabelFieldwiseLeMul_of_pointwiseDependentLabelFieldwiseLeMul
      (Sh := shellShare) (β := β) (H := H)
      (Ω := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω)
      (D :=
        finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v -
          (boundaryCrossingCap n (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω) *
              finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                β H n +
            boundaryCrossingCap n (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω) *
              finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                β H n v +
            finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
              β H n v))
      (ι := ι n v)
      (label := label (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω) v)
      hpointwiseCases

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdExactCardShellBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_residualThresholdSupportExactCardShellBudget15BoundaryCrossingRemainderStrictShare
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardShellBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdExactCardShellBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  rcases hn H hH Ω v hv with
    ⟨shellShare, hshellNonneg, hshareSum, hsupportShell⟩
  refine ⟨shellShare, hshellNonneg, hshareSum, ?_⟩
  exact
    SourceClassEndpointMembershipResidualShellShare15.fieldwiseLeMul_of_supportFieldwiseLeMul
      hv hsupportShell

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_residualThresholdExactCardShellBudget15BoundaryCrossingRemainderStrictShare
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdExactCardShellBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  rcases hn H hH Ω v hv with
    ⟨shellShare, hshellNonneg, hshareSum, hshell⟩
  refine ⟨shellShare.toBudget15, ?_, ?_, ?_⟩
  · exact
      SourceClassEndpointMembershipResidualShellShare15.toBudget15_nonneg
        hshellNonneg
  · simpa [SourceClassEndpointMembershipResidualShellShare15.toBudget15_total]
      using hshareSum
  · exact
      SourceClassEndpointMembershipResidualShellShare15.toBudget15_fieldwiseLeMul
        hshell

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_residualThresholdSupportExactCardShellBudget15BoundaryCrossingRemainderStrictShare
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardShellBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_residualThresholdExactCardShellBudget15BoundaryCrossingRemainderStrictShare
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdExactCardShellBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_residualThresholdSupportExactCardShellBudget15BoundaryCrossingRemainderStrictShare
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_dependentLabelBudget15BoundaryCrossingRemainderStrictShare
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_residualThresholdSupportExactCardShellBudget15BoundaryCrossingRemainderStrictShare
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardShellBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_dependentLabelBudget15BoundaryCrossingRemainderStrictShare
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_pointwiseDependentLabelBudget15BoundaryCrossingRemainderStrictShare
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardPointwiseDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_dependentLabelBudget15BoundaryCrossingRemainderStrictShare
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_pointwiseDependentLabelBudget15BoundaryCrossingRemainderStrictShare
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderAbsorption_of_remainderNonnegative_remainderShare
    (hremainderNonneg :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderNonnegativePositiveSubcritical)
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [
    hremainderNonneg β hβpos hβc,
    hshare β hβpos hβc] with n hnremainderNonneg hnshare
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let B :=
    finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ωnz v
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
  rcases hnshare H hH Ω v hv with
    ⟨sectorShare, _hsectorShareNonneg, hsectorShareSum, hfield⟩
  have hRnonneg : 0 ≤ R := by
    simpa [R, Ωnz, cap, D] using hnremainderNonneg H hH Ω v hv
  have hBtotal : B.total ≤ sectorShare.total * R :=
    SourceClassEndpointMembershipLiveBudget15.total_le_mul_of_fieldwiseLeMul
      hfield
  have hscaled : sectorShare.total * R ≤ R := by
    have hmul : sectorShare.total * R ≤ 1 * R :=
      mul_le_mul_of_nonneg_right hsectorShareSum hRnonneg
    simpa using hmul
  simpa [R, Ωnz, cap, D, B] using hBtotal.trans hscaled

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderAbsorption_of_boundaryCrossingRemainderPositive_remainderShare
    (hremainderPositive :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderAbsorption_of_remainderNonnegative_remainderShare
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderNonnegative_of_boundaryCrossingRemainderPositive
      hremainderPositive)
    hshare

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderAbsorption_of_boundaryCrossingCapComponentSum_remainderShare
    (hcomponent :
      BoundaryCrossingCapComponentSumPositiveSubcritical)
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderAbsorption_of_remainderNonnegative_remainderShare
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderNonnegative_of_boundaryCrossingCapComponentSum
      hcomponent)
    hshare

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentDenominatorFreeSumAbsorption_of_boundaryCrossingRemainder
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let B :=
    finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ωnz v
  have hrem : B.total ≤
      D -
        (cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
              β H n +
          cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
              β H n v +
          finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
            β H n v) := by
    simpa [Ωnz, cap, D, B] using hn H hH Ω v hv
  linarith

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15CanonicalRatioShareSum_of_componentDenominatorFreeSum
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15CanonicalRatioShareSumPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [
    h β hβpos hβc,
    finiteQ2BoundaryVertexDenominatorPositive_from_boxGeometry β hβpos hβc] with
    n hn hnpos
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let B :=
    finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ωnz v
  have hDpos : 0 < D := by
    simpa [D] using hnpos H hH v hv
  have hscalar :
      cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
              β H n +
          cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
              β H n v +
          finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
            β H n v +
          B.total ≤ D := by
    simpa [Ωnz, cap, D, B] using hn H hH Ω v hv
  have hdiv :
      (cap *
              finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                β H n +
            cap *
              finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                β H n v +
            finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
              β H n v +
            B.total) / D ≤ D / D :=
    div_le_div_of_nonneg_right hscalar (le_of_lt hDpos)
  calc
    residualThresholdShellBudget15CanonicalOnePointShare β H n Ωnz v +
          residualThresholdShellBudget15CanonicalBoundaryPairShare
            β H n Ωnz v +
          residualThresholdShellBudget15CanonicalEmptyBoundaryShare
            β H n Ωnz v +
          residualThresholdShellBudget15CanonicalShellBudgetShare
            β H n Ωnz v =
        (cap *
                finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                  β H n +
              cap *
                finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                  β H n v +
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                β H n v +
              B.total) / D := by
      simp [
        residualThresholdShellBudget15CanonicalOnePointShare,
        residualThresholdShellBudget15CanonicalBoundaryPairShare,
        residualThresholdShellBudget15CanonicalEmptyBoundaryShare,
        residualThresholdShellBudget15CanonicalShellBudgetShare,
        cap, D, B]
      ring
    _ ≤ D / D := hdiv
    _ = 1 := by
      field_simp [hDpos.ne']

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15CanonicalRatioShareSum_of_boundaryCrossingRemainder
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15CanonicalRatioShareSumPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15CanonicalRatioShareSum_of_componentDenominatorFreeSum
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentDenominatorFreeSumAbsorption_of_boundaryCrossingRemainder
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentDenominatorFreeSumAbsorption_of_aggregateComponentShare
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [
    h β hβpos hβc,
    finiteQ2BoundaryVertexDenominatorPositive_from_boxGeometry β hβpos hβc] with
    n hn hnpos
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let B :=
    finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ωnz v
  rcases hn H hH Ω v hv with
    ⟨oneShare, boundaryPairShare, emptyBoundaryShare, shellBudgetShare,
      _honeShare, _hboundaryShare, _hemptyShare, _hshellBudgetShare,
      hshareSum, hone, hboundary, hempty, hshell⟩
  have hDnonneg : 0 ≤ D := by
    exact le_of_lt (by simpa [D] using hnpos H hH v hv)
  have hcomponents :
      cap *
              finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                β H n +
            cap *
              finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                β H n v +
            finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
              β H n v +
            B.total ≤
        oneShare * D + boundaryPairShare * D + emptyBoundaryShare * D +
          shellBudgetShare * D := by
    linarith
  have hscaled :
      (oneShare + boundaryPairShare + emptyBoundaryShare +
          shellBudgetShare) * D ≤ D := by
    have hmul :
        (oneShare + boundaryPairShare + emptyBoundaryShare +
            shellBudgetShare) * D ≤ 1 * D :=
      mul_le_mul_of_nonneg_right hshareSum hDnonneg
    simpa using hmul
  calc
    cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
              β H n +
          cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
              β H n v +
          finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
            β H n v +
          B.total ≤
        oneShare * D + boundaryPairShare * D + emptyBoundaryShare * D +
          shellBudgetShare * D := hcomponents
    _ =
        (oneShare + boundaryPairShare + emptyBoundaryShare +
            shellBudgetShare) * D := by
      ring
    _ ≤ D := hscaled

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentDenominatorFreeSumAbsorption_of_canonicalRatioShareSum
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15CanonicalRatioShareSumPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentDenominatorFreeSumAbsorption_of_aggregateComponentShare
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareAbsorption_of_shareSchedule
      (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleAbsorption_of_canonicalRatioShareSum
        h))

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15CanonicalRatioShareSum_iff_componentDenominatorFreeSum :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15CanonicalRatioShareSumPositiveSubcritical ↔
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical :=
  ⟨boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentDenominatorFreeSumAbsorption_of_canonicalRatioShareSum,
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15CanonicalRatioShareSum_of_componentDenominatorFreeSum⟩

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFreeAbsorption_of_residualThresholdShellBudget15StrictComponentDenominatorFreeSum
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictComponentDenominatorFreeSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
        ι label := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let B :=
    finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ωnz v
  refine ⟨B, ?_, ?_⟩
  · exact
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15_fieldwiseLe_residualThresholdShellBudget15_of_boundary
        β H n Ωnz v hv (label Ωnz v)
  · simpa [B, cap, D, Ωnz] using hn H hH Ω v hv

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorption_of_residualThresholdShellBudget15StrictComponentDenominatorFreeSum
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictComponentDenominatorFreeSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorptionPositiveSubcritical
        ι label :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFreeAbsorption_of_residualThresholdShellBudget15StrictComponentDenominatorFreeSum
      (ι := ι) (label := label) h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorption_of_residualThresholdShellBudget15StrictCanonicalRatioShareSum
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictCanonicalRatioShareSumPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorptionPositiveSubcritical
        ι label :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorption_of_residualThresholdShellBudget15StrictComponentDenominatorFreeSum
    (ι := ι) (label := label)
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictComponentDenominatorFreeSumAbsorption_of_strictCanonicalRatioShareSum
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_residualThresholdShellBudget15StrictCanonicalRatioShareSum
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictCanonicalRatioShareSumPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical
        ι label :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorption_of_residualThresholdShellBudget15StrictCanonicalRatioShareSum
      (ι := ι) (label := label) h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeMajorantSumAbsorption_of_residualThresholdShellBudget15ComponentDenominatorFreeSum
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeMajorantSumAbsorptionPositiveSubcritical
        ι label := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let B :=
    finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ωnz v
  refine ⟨B, ?_, ?_⟩
  · exact
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15_fieldwiseLe_residualThresholdShellBudget15_of_boundary
        β H n Ωnz v hv (label Ωnz v)
  · simpa [B, cap, D, Ωnz] using hn H hH Ω v hv

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSumAbsorption_of_residualThresholdShellBudget15ComponentDenominatorFreeSum
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical
        ι label := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let B :=
    finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ωnz v
  let rawShell :=
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawTotal
      v β H Ωnz (ι n v) (label Ωnz v)
  have htotal : B.total = rawShell := by
    simpa [B, rawShell, Ωnz] using
      SourceClassEndpointMembershipResidualShellShare15.residualThresholdShellBudget15_total_eq_normalizedRowsRawTotal_of_boundary
        β H n Ωnz v hv (label Ωnz v)
  simpa [B, rawShell, cap, D, Ωnz, htotal] using hn H hH Ω v hv

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentDenominatorFreeSumAbsorption_of_canonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSum
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let B :=
    finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ωnz v
  let rawShell :=
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawTotal
      v β H Ωnz (ι n v) (label Ωnz v)
  have htotal : B.total = rawShell := by
    simpa [B, rawShell, Ωnz] using
      SourceClassEndpointMembershipResidualShellShare15.residualThresholdShellBudget15_total_eq_normalizedRowsRawTotal_of_boundary
        β H n Ωnz v hv (label Ωnz v)
  simpa [B, rawShell, cap, D, Ωnz, htotal] using hn H hH Ω v hv

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentDenominatorFreeSumAbsorption_iff_canonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSum
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R} :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical ↔
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical
        ι label := by
  constructor
  · exact
      boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSumAbsorption_of_residualThresholdShellBudget15ComponentDenominatorFreeSum
  · exact
      boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentDenominatorFreeSumAbsorption_of_canonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSum

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15CanonicalRatioShareSum_of_residualThresholdShellBudget15CanonicalRatioShareSum
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15CanonicalRatioShareSumPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15CanonicalRatioShareSumPositiveSubcritical
        ι label :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15CanonicalRatioShareSum_of_canonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSum
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSumAbsorption_of_canonicalRawRowDependentLabelBudget15ComponentDenominatorFreeMajorantSum
      (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeMajorantSumAbsorption_of_residualThresholdShellBudget15ComponentDenominatorFreeSum
        (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentDenominatorFreeSumAbsorption_of_canonicalRatioShareSum
          h)))

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSumAbsorption_of_residualThresholdShellBudget15CanonicalRatioShareSum
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15CanonicalRatioShareSumPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical
        ι label :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSumAbsorption_of_canonicalRawRowDependentLabelBudget15CanonicalRatioShareSum
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15CanonicalRatioShareSum_of_residualThresholdShellBudget15CanonicalRatioShareSum
      (ι := ι) (label := label) h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderDenominatorFreeAbsorption_of_residualThresholdShellBudget15CanonicalRatioShareSum
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15CanonicalRatioShareSumPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderDenominatorFreeAbsorptionPositiveSubcritical
        ι label :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15CanonicalRatioShareSum
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15CanonicalRatioShareSum_of_residualThresholdShellBudget15CanonicalRatioShareSum
      (ι := ι) (label := label) h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorption_of_boundaryCrossingCapComponentStrictCanonicalRatioShareSum_residualThresholdShellBudget15CanonicalRatioShareSum
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (hstrict :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hbudgetRatio :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15CanonicalRatioShareSumPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical
        ι label :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorption_of_boundaryCrossingCapComponentStrictCanonicalRatioShareSum_canonicalRawRowDependentLabelBudget15CanonicalRatioShareSum
    hstrict
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15CanonicalRatioShareSum_of_residualThresholdShellBudget15CanonicalRatioShareSum
      (ι := ι) (label := label) hbudgetRatio)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorption_of_residualThresholdShellBudget15StrictCanonicalRatioShareSum
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictCanonicalRatioShareSumPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical
        ι label :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorption_of_boundaryCrossingCapComponentStrictCanonicalRatioShareSum_residualThresholdShellBudget15CanonicalRatioShareSum
    (boundaryCrossingCapComponentStrictCanonicalRatioShareSum_of_residualThresholdShellBudget15StrictCanonicalRatioShareSum
      h)
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15CanonicalRatioShareSum_of_strictCanonicalRatioShareSum
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentSumAbsorption_of_canonicalRawRowDependentLabelBudget15ComponentMajorantSum
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentMajorantSumAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentSumAbsorptionPositiveSubcritical
        ι label := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let rawBudget :=
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15
      v β H Ωnz (ι n v) (label Ωnz v)
  let rawShell :=
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawTotal
      v β H Ωnz (ι n v) (label Ωnz v)
  rcases hn H hH Ω v hv with ⟨B, hDpos, hfield, hsum⟩
  have hrawLe : rawShell ≤ B.total := by
    calc
      rawShell = rawBudget.total := by
        symm
        simpa [rawBudget, rawShell] using
          SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15_total
            (v := v) (β := β) (H := H) (Ω := Ωnz)
            (ι := ι n v) (label := label Ωnz v)
      _ ≤ B.total :=
        SourceClassEndpointMembershipLiveBudget15.total_le_of_fieldwiseLe
          hfield
  refine ⟨hDpos, ?_⟩
  linarith

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15ComponentSumAbsorption_of_canonicalRawRowDependentLabelBudget15ComponentSum
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentSumAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15ComponentSumAbsorptionPositiveSubcritical
        ι label := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let shellShare :=
    SourceClassEndpointMembershipResidualShellShare15.normalizedRows
      v β H D Ωnz (ι n v) (label Ωnz v)
  let rawShell :=
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawTotal
      v β H Ωnz (ι n v) (label Ωnz v)
  rcases hn H hH Ω v hv with ⟨hDpos, hsum⟩
  have hDposD : 0 < D := by
    simpa [D] using hDpos
  have htotal : shellShare.total * D = rawShell := by
    simpa [shellShare, rawShell] using
      SourceClassEndpointMembershipResidualShellShare15.normalizedRows_total_mul_eq_rawTotal
        (v := v) (β := β) (H := H) (D := D) (Ω := Ωnz)
        (ι := ι n v) (label := label Ωnz v) (ne_of_gt hDposD)
  refine ⟨hDpos, ?_⟩
  calc
    cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
              β H n +
          cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
              β H n v +
          finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
            β H n v +
          shellShare.total * D =
        cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
              β H n +
          cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
              β H n v +
          finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
            β H n v +
          rawShell := by
          rw [htotal]
    _ ≤ D := by
      simpa [rawShell, cap, D, Ωnz] using hsum

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentSumAbsorption_of_canonicalNormalizedRowDependentLabelBudget15ComponentSum
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15ComponentSumAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentSumAbsorptionPositiveSubcritical
        ι label := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let shellShare :=
    SourceClassEndpointMembershipResidualShellShare15.normalizedRows
      v β H D Ωnz (ι n v) (label Ωnz v)
  let rawShell :=
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawTotal
      v β H Ωnz (ι n v) (label Ωnz v)
  rcases hn H hH Ω v hv with ⟨hDpos, hsum⟩
  have hDposD : 0 < D := by
    simpa [D] using hDpos
  have htotal : shellShare.total * D = rawShell := by
    simpa [shellShare, rawShell] using
      SourceClassEndpointMembershipResidualShellShare15.normalizedRows_total_mul_eq_rawTotal
        (v := v) (β := β) (H := H) (D := D) (Ω := Ωnz)
        (ι := ι n v) (label := label Ωnz v) (ne_of_gt hDposD)
  refine ⟨hDpos, ?_⟩
  calc
    cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
              β H n +
          cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
              β H n v +
          finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
            β H n v +
          rawShell =
        cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
              β H n +
          cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
              β H n v +
          finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
            β H n v +
          shellShare.total * D := by
          rw [← htotal]
    _ ≤ D := by
      simpa [shellShare, cap, D, Ωnz] using hsum

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15ComponentSumAbsorption_iff_canonicalRawRowDependentLabelBudget15ComponentSum
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R} :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15ComponentSumAbsorptionPositiveSubcritical
        ι label ↔
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentSumAbsorptionPositiveSubcritical
        ι label := by
  constructor
  · exact
      boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentSumAbsorption_of_canonicalNormalizedRowDependentLabelBudget15ComponentSum
  · exact
      boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15ComponentSumAbsorption_of_canonicalRawRowDependentLabelBudget15ComponentSum

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15ComponentShareAbsorption_of_canonicalNormalizedRowDependentLabelBudget15ComponentSum
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15ComponentSumAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15ComponentShareAbsorptionPositiveSubcritical
        ι label := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let shellShare :=
    SourceClassEndpointMembershipResidualShellShare15.normalizedRows
      v β H D Ωnz (ι n v) (label Ωnz v)
  rcases hn H hH Ω v hv with ⟨hDpos, hsum⟩
  have hDposD : 0 < D := by
    simpa [D] using hDpos
  refine ⟨hDpos, ?_⟩
  have hdiv :
      (cap *
              finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                β H n +
            cap *
              finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                β H n v +
            finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
              β H n v +
            shellShare.total * D) / D ≤ D / D :=
    div_le_div_of_nonneg_right hsum (le_of_lt hDposD)
  calc
    cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
              β H n / D +
          cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
              β H n v / D +
          finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
            β H n v / D +
          shellShare.total =
        (cap *
                finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                  β H n +
              cap *
                finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                  β H n v +
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                β H n v +
              shellShare.total * D) / D := by
          field_simp [ne_of_gt hDposD]
    _ ≤ D / D := hdiv
    _ = 1 := by
      exact div_self (ne_of_gt hDposD)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardNormalizedRowDependentLabelBudget15ComponentShareAbsorption_of_canonicalNormalizedRowDependentLabelBudget15ComponentShare
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15ComponentShareAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardNormalizedRowDependentLabelBudget15ComponentShareAbsorptionPositiveSubcritical
        ι label := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let shellShare :=
    SourceClassEndpointMembershipResidualShellShare15.normalizedRows
      v β H D Ωnz (ι n v) (label Ωnz v)
  let oneShare :=
    cap * finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm β H n / D
  let boundaryPairShare :=
    cap *
      finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
        β H n v / D
  let emptyBoundaryShare :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v / D
  rcases hn H hH Ω v hv with ⟨hDpos, hshareSum⟩
  refine
    ⟨oneShare, boundaryPairShare, emptyBoundaryShare, shellShare,
      hDpos, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩
  · have hcap : 0 ≤ cap := by
      simpa [cap, boundaryCrossingCap] using
        finiteBoundaryGhostCollapsedCutoffBoundaryFiberBoundaryCrossingPairCountMultiplicityCap_nonneg
          Ωnz
    have hone :
        0 ≤ finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n :=
      finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm_nonneg
        (le_of_lt hβpos) (le_of_lt hH)
    exact div_nonneg (mul_nonneg hcap hone) (le_of_lt hDpos)
  · have hcap : 0 ≤ cap := by
      simpa [cap, boundaryCrossingCap] using
        finiteBoundaryGhostCollapsedCutoffBoundaryFiberBoundaryCrossingPairCountMultiplicityCap_nonneg
          Ωnz
    have hboundary :
        0 ≤
          finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
            β H n v :=
      finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm_nonneg
        (le_of_lt hβpos) (le_of_lt hH) v
    exact div_nonneg (mul_nonneg hcap hboundary) (le_of_lt hDpos)
  · have hempty :
        0 ≤ finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
          β H n v :=
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm_nonneg
        (le_of_lt hβpos) (le_of_lt hH) v
    exact div_nonneg hempty (le_of_lt hDpos)
  · exact
      SourceClassEndpointMembershipResidualShellShare15.normalizedRows_nonneg
        (v := v) (β := β) (H := H) (D := D) (Ω := Ωnz)
        (ι := ι n v) (label := label Ωnz v)
        (le_of_lt hβpos) (le_of_lt hH) hDpos
  · simpa [oneShare, boundaryPairShare, emptyBoundaryShare, shellShare,
      cap, D, Ωnz] using hshareSum
  · dsimp [oneShare]
    rw [div_mul_cancel₀ _ hDpos.ne']
  · dsimp [boundaryPairShare]
    rw [div_mul_cancel₀ _ hDpos.ne']
  · dsimp [emptyBoundaryShare]
    rw [div_mul_cancel₀ _ hDpos.ne']
  · dsimp [shellShare, SourceClassEndpointMembershipResidualShellShare15.normalizedRows]
    rw [div_mul_cancel₀ _ hDpos.ne']
  · dsimp [shellShare, SourceClassEndpointMembershipResidualShellShare15.normalizedRows]
    rw [div_mul_cancel₀ _ hDpos.ne']
  · dsimp [shellShare, SourceClassEndpointMembershipResidualShellShare15.normalizedRows]
    rw [div_mul_cancel₀ _ hDpos.ne']
  · dsimp [shellShare, SourceClassEndpointMembershipResidualShellShare15.normalizedRows]
    rw [div_mul_cancel₀ _ hDpos.ne']
  · dsimp [shellShare, SourceClassEndpointMembershipResidualShellShare15.normalizedRows]
    rw [div_mul_cancel₀ _ hDpos.ne']
  · dsimp [shellShare, SourceClassEndpointMembershipResidualShellShare15.normalizedRows]
    rw [div_mul_cancel₀ _ hDpos.ne']
  · dsimp [shellShare, SourceClassEndpointMembershipResidualShellShare15.normalizedRows]
    rw [div_mul_cancel₀ _ hDpos.ne']
  · intro hasGhost hasOrigin hasEndpoint k hk
    exact
      SourceClassEndpointMembershipResidualShellShare15.normalizedRows_fourShare
        (v := v) (β := β) (H := H) (D := D) (Ω := Ωnz)
        (ι := ι n v) (label := label Ωnz v)
        hasGhost hasOrigin hasEndpoint k

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardPointwiseDependentLabelBudget15ComponentShareAbsorption_of_normalizedRowDependentLabelBudget15ComponentShare
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardNormalizedRowDependentLabelBudget15ComponentShareAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardPointwiseDependentLabelBudget15ComponentShareAbsorptionPositiveSubcritical
        ι label := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  rcases hn H hH Ω v hv with
    ⟨oneShare, boundaryPairShare, emptyBoundaryShare, shellShare,
      hDpos, honeShare, hboundaryPairShare, hemptyBoundaryShare,
      hshellNonneg, hshareSum, hone, hboundary, hempty,
      hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, hfour⟩
  refine
    ⟨oneShare, boundaryPairShare, emptyBoundaryShare, shellShare,
      honeShare, hboundaryPairShare, hemptyBoundaryShare, hshellNonneg,
      hshareSum, hone, hboundary, hempty, ?_⟩
  exact
    SourceClassEndpointMembershipResidualShellShare15.supportResidualCasePointwiseDependentLabelFieldwiseLeMul_of_normalizedRows
      (Sh := shellShare) (β := β) (H := H)
      (D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v)
      (Ω := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω)
      (ι := ι n v) (label := label (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω) v)
      (le_of_lt hβpos) (le_of_lt hH) hDpos
      hzeroNone htwoNone htwoEndpoint htwoOrigin htwoGhost
      htwoGhostEndpoint htwoGhostOrigin hfour

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardDependentLabelBudget15ComponentShareAbsorption_of_pointwiseDependentLabelBudget15ComponentShare
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardPointwiseDependentLabelBudget15ComponentShareAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardDependentLabelBudget15ComponentShareAbsorptionPositiveSubcritical
        ι label := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  rcases hn H hH Ω v hv with
    ⟨oneShare, boundaryPairShare, emptyBoundaryShare, shellShare,
      honeShare, hboundaryPairShare, hemptyBoundaryShare, hshellNonneg,
      hshareSum, hone, hboundary, hempty, hpointwiseCases⟩
  refine
    ⟨oneShare, boundaryPairShare, emptyBoundaryShare, shellShare,
      honeShare, hboundaryPairShare, hemptyBoundaryShare, hshellNonneg,
      hshareSum, hone, hboundary, hempty, ?_⟩
  exact
    SourceClassEndpointMembershipResidualShellShare15.supportResidualCaseDependentLabelFieldwiseLeMul_of_pointwiseDependentLabelFieldwiseLeMul
      (Sh := shellShare) (β := β) (H := H)
      (Ω := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω)
      (D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v)
      (ι := ι n v) (label := label (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω) v)
      hpointwiseCases

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardResidualCaseBudget15ComponentShareAbsorption_of_dependentLabelBudget15ComponentShare
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardDependentLabelBudget15ComponentShareAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardResidualCaseBudget15ComponentShareAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  rcases hn H hH Ω v hv with
    ⟨oneShare, boundaryPairShare, emptyBoundaryShare, shellShare,
      honeShare, hboundaryPairShare, hemptyBoundaryShare, hshellNonneg,
      hshareSum, hone, hboundary, hempty, hdependentCases⟩
  refine
    ⟨oneShare, boundaryPairShare, emptyBoundaryShare, shellShare,
      honeShare, hboundaryPairShare, hemptyBoundaryShare, hshellNonneg,
      hshareSum, hone, hboundary, hempty, ?_⟩
  exact
    SourceClassEndpointMembershipResidualShellShare15.supportResidualCaseFieldwiseLeMul_of_dependentLabelFieldwiseLeMul
      (Sh := shellShare) (β := β) (H := H)
      (Ω := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω)
      (D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v)
      (ι := ι n v) (label := label (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω) v)
      hdependentCases

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardShellBudget15ComponentShareAbsorption_of_residualThresholdSupportExactCardResidualCaseBudget15ComponentShare
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardResidualCaseBudget15ComponentShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardShellBudget15ComponentShareAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  rcases hn H hH Ω v hv with
    ⟨oneShare, boundaryPairShare, emptyBoundaryShare, shellShare,
      honeShare, hboundaryPairShare, hemptyBoundaryShare, hshellNonneg,
      hshareSum, hone, hboundary, hempty, hresidualCases⟩
  refine
    ⟨oneShare, boundaryPairShare, emptyBoundaryShare, shellShare,
      honeShare, hboundaryPairShare, hemptyBoundaryShare, hshellNonneg,
      hshareSum, hone, hboundary, hempty, ?_⟩
  exact
    SourceClassEndpointMembershipResidualShellShare15.supportFieldwiseLeMul_of_residualCaseFieldwiseLeMul
      hv hresidualCases

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardShellBudget15ComponentShareAbsorption_of_dependentLabelBudget15ComponentShare
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardDependentLabelBudget15ComponentShareAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardShellBudget15ComponentShareAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardShellBudget15ComponentShareAbsorption_of_residualThresholdSupportExactCardResidualCaseBudget15ComponentShare
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardResidualCaseBudget15ComponentShareAbsorption_of_dependentLabelBudget15ComponentShare
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdExactCardShellBudget15ComponentShareAbsorption_of_residualThresholdSupportExactCardShellBudget15ComponentShare
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardShellBudget15ComponentShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdExactCardShellBudget15ComponentShareAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  rcases hn H hH Ω v hv with
    ⟨oneShare, boundaryPairShare, emptyBoundaryShare, shellShare,
      honeShare, hboundaryPairShare, hemptyBoundaryShare, hshellNonneg,
      hshareSum, hone, hboundary, hempty, hsupportShell⟩
  refine
    ⟨oneShare, boundaryPairShare, emptyBoundaryShare, shellShare,
      honeShare, hboundaryPairShare, hemptyBoundaryShare, hshellNonneg,
      hshareSum, hone, hboundary, hempty, ?_⟩
  exact
    SourceClassEndpointMembershipResidualShellShare15.fieldwiseLeMul_of_supportFieldwiseLeMul
      hv hsupportShell

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentShareAbsorption_of_residualThresholdExactCardShellBudget15ComponentShare
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdExactCardShellBudget15ComponentShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentShareAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  rcases hn H hH Ω v hv with
    ⟨oneShare, boundaryPairShare, emptyBoundaryShare, shellShare,
      honeShare, hboundaryPairShare, hemptyBoundaryShare, hshellNonneg,
      hshareSum, hone, hboundary, hempty, hshell⟩
  refine
    ⟨oneShare, boundaryPairShare, emptyBoundaryShare, shellShare.toBudget15,
      honeShare, hboundaryPairShare, hemptyBoundaryShare, ?_, ?_, hone,
      hboundary, hempty, ?_⟩
  · exact
      SourceClassEndpointMembershipResidualShellShare15.toBudget15_nonneg
        hshellNonneg
  · simpa [SourceClassEndpointMembershipResidualShellShare15.toBudget15_total]
      using hshareSum
  · exact
      SourceClassEndpointMembershipResidualShellShare15.toBudget15_fieldwiseLeMul
        hshell

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentShareAbsorption_of_residualThresholdSupportExactCardShellBudget15ComponentShare
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardShellBudget15ComponentShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentShareAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentShareAbsorption_of_residualThresholdExactCardShellBudget15ComponentShare
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdExactCardShellBudget15ComponentShareAbsorption_of_residualThresholdSupportExactCardShellBudget15ComponentShare
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdBudget15ComponentShareAbsorption_of_residualThresholdShellBudget15ComponentShare
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdBudget15ComponentShareAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let B :=
    finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdBudget15
      β H n Ωnz v
  let Bshell :=
    finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ωnz v
  rcases hn H hH Ω v hv with
    ⟨oneShare, boundaryPairShare, emptyBoundaryShare, sectorShare,
      honeShare, hboundaryPairShare, hemptyBoundaryShare, hsectorShare,
      hshareSum, hone, hboundary, hempty, hshell⟩
  rcases hshell with
    ⟨hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, hfourNone, hfourEndpoint,
      hfourOrigin, hfourOriginEndpoint, hfourGhost, hfourGhostEndpoint,
      hfourGhostOrigin, hfourGhostOriginEndpoint⟩
  refine
    ⟨oneShare, boundaryPairShare, emptyBoundaryShare, sectorShare,
      honeShare, hboundaryPairShare, hemptyBoundaryShare, hsectorShare,
      hshareSum, hone, hboundary, hempty, ?_⟩
  refine
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [B, Bshell,
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
      using hzeroNone
  · simpa [B, Bshell,
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
      using htwoNone
  · simpa [B, Bshell,
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
      using htwoEndpoint
  · simpa [B, Bshell,
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
      using htwoOrigin
  · simpa [B, Bshell,
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
      using htwoGhost
  · simpa [B, Bshell,
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
      using htwoGhostEndpoint
  · simpa [B, Bshell,
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
      using htwoGhostOrigin
  · exact
      (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdImageSourceClassSum_le_thresholdShellImageSourceClassSum
        (le_of_lt hβpos) (le_of_lt hH) n Ωnz v false false false).trans
        (by
          simpa [B, Bshell,
            finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdBudget15,
            finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
            finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
            using hfourNone)
  · exact
      (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdImageSourceClassSum_le_thresholdShellImageSourceClassSum
        (le_of_lt hβpos) (le_of_lt hH) n Ωnz v false false true).trans
        (by
          simpa [B, Bshell,
            finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdBudget15,
            finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
            finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
            using hfourEndpoint)
  · exact
      (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdImageSourceClassSum_le_thresholdShellImageSourceClassSum
        (le_of_lt hβpos) (le_of_lt hH) n Ωnz v false true false).trans
        (by
          simpa [B, Bshell,
            finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdBudget15,
            finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
            finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
            using hfourOrigin)
  · exact
      (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdImageSourceClassSum_le_thresholdShellImageSourceClassSum
        (le_of_lt hβpos) (le_of_lt hH) n Ωnz v false true true).trans
        (by
          simpa [B, Bshell,
            finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdBudget15,
            finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
            finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
            using hfourOriginEndpoint)
  · exact
      (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdImageSourceClassSum_le_thresholdShellImageSourceClassSum
        (le_of_lt hβpos) (le_of_lt hH) n Ωnz v true false false).trans
        (by
          simpa [B, Bshell,
            finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdBudget15,
            finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
            finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
            using hfourGhost)
  · exact
      (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdImageSourceClassSum_le_thresholdShellImageSourceClassSum
        (le_of_lt hβpos) (le_of_lt hH) n Ωnz v true false true).trans
        (by
          simpa [B, Bshell,
            finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdBudget15,
            finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
            finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
            using hfourGhostEndpoint)
  · exact
      (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdImageSourceClassSum_le_thresholdShellImageSourceClassSum
        (le_of_lt hβpos) (le_of_lt hH) n Ωnz v true true false).trans
        (by
          simpa [B, Bshell,
            finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdBudget15,
            finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
            finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
            using hfourGhostOrigin)
  · exact
      (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdImageSourceClassSum_le_thresholdShellImageSourceClassSum
        (le_of_lt hβpos) (le_of_lt hH) n Ωnz v true true true).trans
        (by
          simpa [B, Bshell,
            finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdBudget15,
            finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
            finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
            using hfourGhostOriginEndpoint)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdBudget15ComponentShareAbsorption_of_residualThresholdExactCardShellBudget15ComponentShare
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdExactCardShellBudget15ComponentShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdBudget15ComponentShareAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdBudget15ComponentShareAbsorption_of_residualThresholdShellBudget15ComponentShare
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentShareAbsorption_of_residualThresholdExactCardShellBudget15ComponentShare
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdBudget15ComponentShareAbsorption_of_residualThresholdSupportExactCardShellBudget15ComponentShare
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardShellBudget15ComponentShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdBudget15ComponentShareAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdBudget15ComponentShareAbsorption_of_residualThresholdExactCardShellBudget15ComponentShare
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdExactCardShellBudget15ComponentShareAbsorption_of_residualThresholdSupportExactCardShellBudget15ComponentShare
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdBudget15ComponentSumAbsorption_of_residualThresholdBudget15ComponentShare
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdBudget15ComponentShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdBudget15ComponentSumAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let B :=
    finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdBudget15
      β H n Ωnz v
  rcases hn H hH Ω v hv with
    ⟨oneShare, boundaryPairShare, emptyBoundaryShare, sectorShare,
      _honeShare, _hboundaryPairShare, _hemptyBoundaryShare,
      _hsectorShare, hshareSum, hone, hboundary, hempty, hsector⟩
  have hD : 0 ≤ D := by
    dsimp [D]
    exact finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct_nonneg
      (β := β) (H := H) (n := n) (le_of_lt hβpos) (le_of_lt hH) v
  have hsectorTotal :
      B.total ≤ sectorShare.total * D :=
    SourceClassEndpointMembershipLiveBudget15.total_le_mul_of_fieldwiseLeMul
      hsector
  calc
    cap *
          finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
            β H n +
        cap *
          finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
            β H n v +
        finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v +
        B.total
        ≤
          oneShare * D + boundaryPairShare * D +
            emptyBoundaryShare * D + sectorShare.total * D := by
          exact
            add_le_add (add_le_add (add_le_add hone hboundary) hempty)
              hsectorTotal
    _ =
        (oneShare + boundaryPairShare + emptyBoundaryShare +
            sectorShare.total) * D := by
      ring
    _ ≤ 1 * D := mul_le_mul_of_nonneg_right hshareSum hD
    _ =
        finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v := by
      simp [D]

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualBudget15ComponentSumAbsorption_of_residualThresholdBudget15
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdBudget15ComponentSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualBudget15ComponentSumAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  have htotal :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualBudget15
          β H n Ωnz v).total =
        (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdBudget15
          β H n Ωnz v).total :=
    finiteBoundaryGhostSourceClassEndpointMembershipResidualBudget15_total_eq_threshold_total
      β H n Ωnz v hv
  simpa [Ωnz, htotal] using hn H hH Ω v hv

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualBudget15ComponentSumAbsorption_of_residualThresholdBudget15ComponentShare
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdBudget15ComponentShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualBudget15ComponentSumAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualBudget15ComponentSumAbsorption_of_residualThresholdBudget15
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdBudget15ComponentSumAbsorption_of_residualThresholdBudget15ComponentShare
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualBudget15ComponentSumAbsorption_of_residualThresholdShellBudget15ComponentShare
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualBudget15ComponentSumAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualBudget15ComponentSumAbsorption_of_residualThresholdBudget15ComponentShare
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdBudget15ComponentShareAbsorption_of_residualThresholdShellBudget15ComponentShare
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualBudget15ComponentSumAbsorption_of_residualThresholdExactCardShellBudget15ComponentShare
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdExactCardShellBudget15ComponentShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualBudget15ComponentSumAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualBudget15ComponentSumAbsorption_of_residualThresholdShellBudget15ComponentShare
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentShareAbsorption_of_residualThresholdExactCardShellBudget15ComponentShare
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualBudget15ComponentSumAbsorption_of_residualThresholdSupportExactCardShellBudget15ComponentShare
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardShellBudget15ComponentShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualBudget15ComponentSumAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualBudget15ComponentSumAbsorption_of_residualThresholdExactCardShellBudget15ComponentShare
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdExactCardShellBudget15ComponentShareAbsorption_of_residualThresholdSupportExactCardShellBudget15ComponentShare
      h)

end Exact3D
end StatMech
