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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part116
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitRowEnvelopeCardMajorantStrictMajorantDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitRowEnvelopeClassifiedCardStrictMajorantDenominatorFree
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
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitRowEnvelopeClassifiedCardStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitRowEnvelopeCardMajorantStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
        ι label := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  rcases hn H hH Ω v hv with
    ⟨zeroNone, twoNone, twoEndpoint, twoOrigin, twoGhost,
      twoGhostEndpoint, twoGhostOrigin, rowEnvelope, hzeroNone,
      htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, henv, henvNonneg,
      hbudget⟩
  let cardMajorant :
      ∀ hasGhost hasOrigin hasEndpoint
        (R : Finset (Option (FK.boxVerts 3 n))),
        ι n v hasGhost hasOrigin hasEndpoint R → ℝ :=
    fun hasGhost hasOrigin hasEndpoint R _i =>
      ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
        v Ωnz hasGhost hasOrigin hasEndpoint R).card : ℝ)
  refine
    ⟨zeroNone, twoNone, twoEndpoint, twoOrigin, twoGhost,
      twoGhostEndpoint, twoGhostOrigin, rowEnvelope, cardMajorant,
      hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, henv, ?_, henvNonneg, ?_⟩
  · intro hasGhost hasOrigin hasEndpoint k _hk R _hR i
    exact
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet_card_le_classifiedSet_card
        v Ωnz hasGhost hasOrigin hasEndpoint R
        (label Ωnz v hasGhost hasOrigin hasEndpoint R) i
  · simpa [cardMajorant, Ωnz] using hbudget

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitRowStrictMajorantDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitRowEnvelopeCardMajorantStrictMajorantDenominatorFree
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
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitRowEnvelopeCardMajorantStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitRowStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
        ι label := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  rcases hn H hH Ω v hv with
    ⟨zeroNone, twoNone, twoEndpoint, twoOrigin, twoGhost,
      twoGhostEndpoint, twoGhostOrigin, rowEnvelope, cardMajorant,
      hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, henv, hcard, henvNonneg,
      hbudget⟩
  let rowMajorant :
      ∀ hasGhost hasOrigin hasEndpoint
        (R : Finset (Option (FK.boxVerts 3 n))),
        ι n v hasGhost hasOrigin hasEndpoint R → ℝ :=
    fun hasGhost hasOrigin hasEndpoint R i =>
      cardMajorant hasGhost hasOrigin hasEndpoint R i *
        rowEnvelope hasGhost hasOrigin hasEndpoint R i
  refine
    ⟨zeroNone, twoNone, twoEndpoint, twoOrigin, twoGhost,
      twoGhostEndpoint, twoGhostOrigin, rowMajorant, hzeroNone,
      htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, ?_, ?_⟩
  · intro hasGhost hasOrigin hasEndpoint k hk R hR i
    have hsum :
        (∑ E ∈
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
            v Ωnz hasGhost hasOrigin hasEndpoint R
            (label Ωnz v hasGhost hasOrigin hasEndpoint R) i,
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
            β H E) ≤
          ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
              v Ωnz hasGhost hasOrigin hasEndpoint R
              (label Ωnz v hasGhost hasOrigin hasEndpoint R) i).card : ℝ) *
            rowEnvelope hasGhost hasOrigin hasEndpoint R i := by
      have hsum' :
          (∑ E ∈
            finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
              v Ωnz hasGhost hasOrigin hasEndpoint R
              (label Ωnz v hasGhost hasOrigin hasEndpoint R) i,
            finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
              β H E) ≤
            ∑ E ∈
              finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
                v Ωnz hasGhost hasOrigin hasEndpoint R
                (label Ωnz v hasGhost hasOrigin hasEndpoint R) i,
              rowEnvelope hasGhost hasOrigin hasEndpoint R i := by
        exact
          Finset.sum_le_sum fun E hE =>
            henv hasGhost hasOrigin hasEndpoint k hk R hR i E hE
      simpa [Finset.sum_const, nsmul_eq_mul] using hsum'
    exact
      le_trans hsum
        (by
          simpa [rowMajorant] using
            mul_le_mul_of_nonneg_right
              (hcard hasGhost hasOrigin hasEndpoint k hk R hR i)
              (henvNonneg hasGhost hasOrigin hasEndpoint k hk R hR i))
  · simpa [rowMajorant, Ωnz] using hbudget

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitRowStrictMajorantDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitRowEnvelopeStrictMajorantDenominatorFree
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
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitRowEnvelopeStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitRowStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
        ι label := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  rcases hn H hH Ω v hv with
    ⟨zeroNone, twoNone, twoEndpoint, twoOrigin, twoGhost,
      twoGhostEndpoint, twoGhostOrigin, rowEnvelope, hzeroNone,
      htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, henv, hbudget⟩
  let rowMajorant :
      ∀ hasGhost hasOrigin hasEndpoint
        (R : Finset (Option (FK.boxVerts 3 n))),
        ι n v hasGhost hasOrigin hasEndpoint R → ℝ :=
    fun hasGhost hasOrigin hasEndpoint R i =>
      ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
          v Ωnz hasGhost hasOrigin hasEndpoint R
          (label Ωnz v hasGhost hasOrigin hasEndpoint R) i).card : ℝ) *
        rowEnvelope hasGhost hasOrigin hasEndpoint R i
  refine
    ⟨zeroNone, twoNone, twoEndpoint, twoOrigin, twoGhost,
      twoGhostEndpoint, twoGhostOrigin, rowMajorant, hzeroNone,
      htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, ?_, ?_⟩
  · intro hasGhost hasOrigin hasEndpoint k hk R hR i
    have hrow :
        (∑ E ∈
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
            v Ωnz hasGhost hasOrigin hasEndpoint R
            (label Ωnz v hasGhost hasOrigin hasEndpoint R) i,
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
            β H E) ≤
          ∑ E ∈
            finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
              v Ωnz hasGhost hasOrigin hasEndpoint R
              (label Ωnz v hasGhost hasOrigin hasEndpoint R) i,
            rowEnvelope hasGhost hasOrigin hasEndpoint R i := by
      exact
        Finset.sum_le_sum fun E hE =>
          henv hasGhost hasOrigin hasEndpoint k hk R hR i E hE
    simpa [rowMajorant, Finset.sum_const, nsmul_eq_mul] using hrow
  · simpa [rowMajorant, Ωnz] using hbudget

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitRowStrictMajorantDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitPointwiseStrictMajorantDenominatorFree
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
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitPointwiseStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitRowStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
        ι label := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  rcases hn H hH Ω v hv with
    ⟨zeroNone, twoNone, twoEndpoint, twoOrigin, twoGhost,
      twoGhostEndpoint, twoGhostOrigin, pointMajorant, hzeroNone,
      htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, hpoint, hsum⟩
  let rowMajorant :
      ∀ hasGhost hasOrigin hasEndpoint
        (R : Finset (Option (FK.boxVerts 3 n))),
        ι n v hasGhost hasOrigin hasEndpoint R → ℝ :=
    fun hasGhost hasOrigin hasEndpoint R i =>
      ∑ E ∈
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
          v Ωnz hasGhost hasOrigin hasEndpoint R
          (label Ωnz v hasGhost hasOrigin hasEndpoint R) i,
        pointMajorant hasGhost hasOrigin hasEndpoint R i E
  refine
    ⟨zeroNone, twoNone, twoEndpoint, twoOrigin, twoGhost,
      twoGhostEndpoint, twoGhostOrigin, rowMajorant, hzeroNone,
      htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, ?_, ?_⟩
  · intro hasGhost hasOrigin hasEndpoint k hk R hR i
    exact
      Finset.sum_le_sum fun E hE =>
        hpoint hasGhost hasOrigin hasEndpoint k hk R hR i E hE
  · simpa [rowMajorant, Ωnz] using hsum

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitResidualEnvelopeClassifiedCardStrictMajorantDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitLabelFreeResidualEnvelopeClassifiedCardStrictMajorantDenominatorFree
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
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitLabelFreeResidualEnvelopeClassifiedCardStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitResidualEnvelopeClassifiedCardStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
        ι label := by
  intro β hβpos hβc
  exact h β hβpos hβc

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExplicitStrictMajorantDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitLabelFreeResidualEnvelopeClassifiedCardStrictMajorantDenominatorFree
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitLabelFreeResidualEnvelopeClassifiedCardStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExplicitStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  rcases hn H hH Ω v hv with
    ⟨zeroNone, twoNone, twoEndpoint, twoOrigin, twoGhost,
      twoGhostEndpoint, twoGhostOrigin, residualEnvelope, hzeroNone,
      htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, henv, hbudget⟩
  let fourMajorant : Bool → Bool → Bool → ℕ → ℝ :=
    fun hasGhost hasOrigin hasEndpoint k =>
      ∑ R ∈
        finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
          v k,
        ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
            v Ωnz hasGhost hasOrigin hasEndpoint R).card : ℝ) *
          residualEnvelope hasGhost hasOrigin hasEndpoint R
  refine
    ⟨zeroNone, twoNone, twoEndpoint, twoOrigin, twoGhost,
      twoGhostEndpoint, twoGhostOrigin, fourMajorant, hzeroNone,
      htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, ?_, ?_⟩
  · intro hasGhost hasOrigin hasEndpoint k hk
    exact
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare_le_residualEnvelopeClassifiedCardSum
        (v := v) (β := β) (H := H) (Ω := Ωnz)
        (residualEnvelope := residualEnvelope)
        (hasGhost := hasGhost) (hasOrigin := hasOrigin)
        (hasEndpoint := hasEndpoint) (k := k)
        (henv hasGhost hasOrigin hasEndpoint k hk)
  · simpa [fourMajorant, Ωnz] using hbudget

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExpandedStrictMajorantDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitLabelFreeResidualEnvelopeClassifiedCardStrictMajorantDenominatorFree
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitLabelFreeResidualEnvelopeClassifiedCardStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExpandedStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  rcases hn H hH Ω v hv with
    ⟨zeroNone, twoNone, twoEndpoint, twoOrigin, twoGhost,
      twoGhostEndpoint, twoGhostOrigin, residualEnvelope, hzeroNone,
      htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, henv, hbudget⟩
  let fourMajorant : Bool → Bool → Bool → ℕ → ℝ :=
    fun hasGhost hasOrigin hasEndpoint k =>
      ∑ R ∈
        finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
          v k,
        ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
            v Ωnz hasGhost hasOrigin hasEndpoint R).card : ℝ) *
          residualEnvelope hasGhost hasOrigin hasEndpoint R
  refine
    ⟨zeroNone, twoNone, twoEndpoint, twoOrigin, twoGhost,
      twoGhostEndpoint, twoGhostOrigin, fourMajorant, hzeroNone,
      htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, ?_, ?_⟩
  · intro hasGhost hasOrigin hasEndpoint k hk
    exact
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare_le_residualEnvelopeClassifiedCardSum
        (v := v) (β := β) (H := H) (Ω := Ωnz)
        (residualEnvelope := residualEnvelope)
        (hasGhost := hasGhost) (hasOrigin := hasOrigin)
        (hasEndpoint := hasEndpoint) (k := k)
        (henv hasGhost hasOrigin hasEndpoint k hk)
  · simpa [
      fourMajorant,
      SourceClassEndpointMembershipResidualShellShare15.ofFourShare_total,
      Ωnz] using hbudget

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExpandedStrictMajorantDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedResidualEnvelopeClassifiedCardExpandedStrictMajorantDenominatorFree
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedResidualEnvelopeClassifiedCardExpandedStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExpandedStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  rcases hn H hH Ω v hv with
    ⟨zeroNone, twoNone, twoEndpoint, twoOrigin, twoGhost,
      twoGhostEndpoint, twoGhostOrigin, residualEnvelope, hzeroNone,
      htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, henv, hbudget⟩
  let fourMajorant : Bool → Bool → Bool → ℕ → ℝ :=
    SourceClassEndpointMembershipResidualShellShare15.residualEnvelopeClassifiedCardFourMajorant
      v Ωnz residualEnvelope
  refine
    ⟨zeroNone, twoNone, twoEndpoint, twoOrigin, twoGhost,
      twoGhostEndpoint, twoGhostOrigin, fourMajorant, hzeroNone,
      htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, ?_, ?_⟩
  · intro hasGhost hasOrigin hasEndpoint k hk
    exact
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare_le_residualEnvelopeClassifiedCardFourMajorant
        (v := v) (β := β) (H := H) (Ω := Ωnz)
        (residualEnvelope := residualEnvelope)
        (hasGhost := hasGhost) (hasOrigin := hasOrigin)
        (hasEndpoint := hasEndpoint) (k := k)
        (henv hasGhost hasOrigin hasEndpoint k hk)
  · simpa [
      fourMajorant,
      SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal,
      Ωnz] using hbudget

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedResidualEnvelopeClassifiedCardExpandedStrictMajorantDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedResidualEnvelopeClassifiedCardCanonicalExpandedStrictRemainder
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedResidualEnvelopeClassifiedCardCanonicalExpandedStrictRemainderAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedResidualEnvelopeClassifiedCardExpandedStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
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
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  rcases hn H hH Ω v hv with
    ⟨residualEnvelope, henv, hbudget⟩
  refine
    ⟨B.zero_none, B.two_none, B.two_endpoint, B.two_origin,
      B.two_ghost, B.two_ghost_endpoint, B.two_ghost_origin,
      residualEnvelope, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl,
      le_rfl, le_rfl, henv, ?_⟩
  have hbudget' :
      paid +
          SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal
            v B.zero_none B.two_none B.two_endpoint B.two_origin
            B.two_ghost B.two_ghost_endpoint B.two_ghost_origin
            (SourceClassEndpointMembershipResidualShellShare15.residualEnvelopeClassifiedCardFourMajorant
              v Ωnz residualEnvelope) <
        D := by
    linarith
  simpa [paid, B, Ωnz, D, cap] using hbudget'

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExpandedStrictMajorantDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedResidualEnvelopeClassifiedCardCanonicalExpandedStrictRemainder
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedResidualEnvelopeClassifiedCardCanonicalExpandedStrictRemainderAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExpandedStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExpandedStrictMajorantDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedResidualEnvelopeClassifiedCardExpandedStrictMajorantDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedResidualEnvelopeClassifiedCardExpandedStrictMajorantDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedResidualEnvelopeClassifiedCardCanonicalExpandedStrictRemainder
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitStrictMajorantDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitResidualEnvelopeClassifiedCardStrictMajorantDenominatorFree
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
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitResidualEnvelopeClassifiedCardStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
        ι label := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  rcases hn H hH Ω v hv with
    ⟨zeroNone, twoNone, twoEndpoint, twoOrigin, twoGhost,
      twoGhostEndpoint, twoGhostOrigin, residualEnvelope, hzeroNone,
      htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, henv, hbudget⟩
  let fourMajorant : Bool → Bool → Bool → ℕ → ℝ :=
    fun hasGhost hasOrigin hasEndpoint k =>
      ∑ R ∈
        finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
          v k,
        ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
            v Ωnz hasGhost hasOrigin hasEndpoint R).card : ℝ) *
          residualEnvelope hasGhost hasOrigin hasEndpoint R
  refine
    ⟨zeroNone, twoNone, twoEndpoint, twoOrigin, twoGhost,
      twoGhostEndpoint, twoGhostOrigin, fourMajorant, hzeroNone,
      htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, ?_, ?_⟩
  · intro hasGhost hasOrigin hasEndpoint k hk
    exact
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_le_residualEnvelopeClassifiedCardSum
        (v := v) (β := β) (H := H) (Ω := Ωnz)
        (ι := ι n v) (label := label Ωnz v)
        (residualEnvelope := residualEnvelope)
        (hasGhost := hasGhost) (hasOrigin := hasOrigin)
        (hasEndpoint := hasEndpoint) (k := k)
        (henv hasGhost hasOrigin hasEndpoint k hk)
  · simpa [fourMajorant, Ωnz] using hbudget

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExplicitStrictMajorantDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitLabelFreePointwiseClassifiedStrictMajorantDenominatorFree
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitLabelFreePointwiseClassifiedStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExplicitStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  rcases hn H hH Ω v hv with
    ⟨zeroNone, twoNone, twoEndpoint, twoOrigin, twoGhost,
      twoGhostEndpoint, twoGhostOrigin, pointMajorant, hzeroNone,
      htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, hpoint, hbudget⟩
  let fourMajorant : Bool → Bool → Bool → ℕ → ℝ :=
    fun hasGhost hasOrigin hasEndpoint k =>
      ∑ R ∈
        finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
          v k,
        ∑ E ∈
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
            v Ωnz hasGhost hasOrigin hasEndpoint R,
          pointMajorant hasGhost hasOrigin hasEndpoint R E
  refine
    ⟨zeroNone, twoNone, twoEndpoint, twoOrigin, twoGhost,
      twoGhostEndpoint, twoGhostOrigin, fourMajorant, hzeroNone,
      htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, ?_, ?_⟩
  · intro hasGhost hasOrigin hasEndpoint k hk
    exact
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare_le_classifiedSetPointMajorantSum
        (v := v) (β := β) (H := H) (Ω := Ωnz)
        (pointMajorant := pointMajorant)
        (hasGhost := hasGhost) (hasOrigin := hasOrigin)
        (hasEndpoint := hasEndpoint) (k := k)
        (hpoint hasGhost hasOrigin hasEndpoint k hk)
  · simpa [fourMajorant, Ωnz] using hbudget

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExpandedStrictMajorantDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitLabelFreePointwiseClassifiedStrictMajorantDenominatorFree
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitLabelFreePointwiseClassifiedStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExpandedStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  rcases hn H hH Ω v hv with
    ⟨zeroNone, twoNone, twoEndpoint, twoOrigin, twoGhost,
      twoGhostEndpoint, twoGhostOrigin, pointMajorant, hzeroNone,
      htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, hpoint, hbudget⟩
  let fourMajorant : Bool → Bool → Bool → ℕ → ℝ :=
    fun hasGhost hasOrigin hasEndpoint k =>
      ∑ R ∈
        finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
          v k,
        ∑ E ∈
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
            v Ωnz hasGhost hasOrigin hasEndpoint R,
          pointMajorant hasGhost hasOrigin hasEndpoint R E
  refine
    ⟨zeroNone, twoNone, twoEndpoint, twoOrigin, twoGhost,
      twoGhostEndpoint, twoGhostOrigin, fourMajorant, hzeroNone,
      htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, ?_, ?_⟩
  · intro hasGhost hasOrigin hasEndpoint k hk
    exact
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare_le_classifiedSetPointMajorantSum
        (v := v) (β := β) (H := H) (Ω := Ωnz)
        (pointMajorant := pointMajorant)
        (hasGhost := hasGhost) (hasOrigin := hasOrigin)
        (hasEndpoint := hasEndpoint) (k := k)
        (hpoint hasGhost hasOrigin hasEndpoint k hk)
  · simpa [
      fourMajorant,
      SourceClassEndpointMembershipResidualShellShare15.ofFourShare_total,
      Ωnz] using hbudget

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExpandedStrictMajorantDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedPointwiseClassifiedExpandedStrictMajorantDenominatorFree
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedPointwiseClassifiedExpandedStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExpandedStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  rcases hn H hH Ω v hv with
    ⟨zeroNone, twoNone, twoEndpoint, twoOrigin, twoGhost,
      twoGhostEndpoint, twoGhostOrigin, pointMajorant, hzeroNone,
      htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, hpoint, hbudget⟩
  let fourMajorant : Bool → Bool → Bool → ℕ → ℝ :=
    SourceClassEndpointMembershipResidualShellShare15.pointwiseClassifiedFourMajorant
      v Ωnz pointMajorant
  refine
    ⟨zeroNone, twoNone, twoEndpoint, twoOrigin, twoGhost,
      twoGhostEndpoint, twoGhostOrigin, fourMajorant, hzeroNone,
      htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, ?_, ?_⟩
  · intro hasGhost hasOrigin hasEndpoint k hk
    exact
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare_le_pointwiseClassifiedFourMajorant
        (v := v) (β := β) (H := H) (Ω := Ωnz)
        (pointMajorant := pointMajorant)
        (hasGhost := hasGhost) (hasOrigin := hasOrigin)
        (hasEndpoint := hasEndpoint) (k := k)
        (hpoint hasGhost hasOrigin hasEndpoint k hk)
  · simpa [
      fourMajorant,
      SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal,
      Ωnz] using hbudget

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedPointwiseClassifiedExpandedStrictMajorantDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedPointwiseClassifiedCanonicalExpandedStrictRemainder
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedPointwiseClassifiedCanonicalExpandedStrictRemainderAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedPointwiseClassifiedExpandedStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
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
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  rcases hn H hH Ω v hv with
    ⟨pointMajorant, hpoint, hbudget⟩
  refine
    ⟨B.zero_none, B.two_none, B.two_endpoint, B.two_origin,
      B.two_ghost, B.two_ghost_endpoint, B.two_ghost_origin,
      pointMajorant, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl,
      le_rfl, le_rfl, hpoint, ?_⟩
  have hbudget' :
      paid +
          SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal
            v B.zero_none B.two_none B.two_endpoint B.two_origin
            B.two_ghost B.two_ghost_endpoint B.two_ghost_origin
            (SourceClassEndpointMembershipResidualShellShare15.pointwiseClassifiedFourMajorant
              v Ωnz pointMajorant) <
        D := by
    linarith
  simpa [paid, B, Ωnz, D, cap] using hbudget'

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExpandedStrictMajorantDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedPointwiseClassifiedCanonicalExpandedStrictRemainder
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedPointwiseClassifiedCanonicalExpandedStrictRemainderAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExpandedStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExpandedStrictMajorantDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedPointwiseClassifiedExpandedStrictMajorantDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedPointwiseClassifiedExpandedStrictMajorantDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedPointwiseClassifiedCanonicalExpandedStrictRemainder
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositive_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedResidualEnvelopeClassifiedCardCanonicalExpandedStrictRemainder
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedResidualEnvelopeClassifiedCardCanonicalExpandedStrictRemainderAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
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
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  rcases hn H hH Ω v hv with
    ⟨residualEnvelope, henv, hbudget⟩
  have hB :=
    finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15_nonneg
      (le_of_lt hβpos) (le_of_lt hH) n Ωnz v
  rcases hB with
    ⟨hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, _hfourNone, _hfourEndpoint,
      _hfourOrigin, _hfourOriginEndpoint, _hfourGhost,
      _hfourGhostEndpoint, _hfourGhostOrigin, _hfourGhostOriginEndpoint⟩
  have htotalNonneg :
      0 ≤
        SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal
          v B.zero_none B.two_none B.two_endpoint B.two_origin
          B.two_ghost B.two_ghost_endpoint B.two_ghost_origin
          (SourceClassEndpointMembershipResidualShellShare15.residualEnvelopeClassifiedCardFourMajorant
            v Ωnz residualEnvelope) := by
    exact
      SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal_nonneg_of_residualEnvelopeClassifiedCardFourMajorant_summandBounds
        (β := β) (H := H) (v := v) (Ω := Ωnz)
        (residualEnvelope := residualEnvelope)
        (le_of_lt hβpos) (le_of_lt hH)
        hzeroNone htwoNone htwoEndpoint htwoOrigin htwoGhost
        htwoGhostEndpoint htwoGhostOrigin henv
  have hrem : 0 < D - paid := lt_of_le_of_lt htotalNonneg hbudget
  simpa [paid, B, Ωnz, D, cap] using hrem

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositive_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedPointwiseClassifiedCanonicalExpandedStrictRemainder
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedPointwiseClassifiedCanonicalExpandedStrictRemainderAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
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
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  rcases hn H hH Ω v hv with
    ⟨pointMajorant, hpoint, hbudget⟩
  have hB :=
    finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15_nonneg
      (le_of_lt hβpos) (le_of_lt hH) n Ωnz v
  rcases hB with
    ⟨hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, _hfourNone, _hfourEndpoint,
      _hfourOrigin, _hfourOriginEndpoint, _hfourGhost,
      _hfourGhostEndpoint, _hfourGhostOrigin, _hfourGhostOriginEndpoint⟩
  have htotalNonneg :
      0 ≤
        SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal
          v B.zero_none B.two_none B.two_endpoint B.two_origin
          B.two_ghost B.two_ghost_endpoint B.two_ghost_origin
          (SourceClassEndpointMembershipResidualShellShare15.pointwiseClassifiedFourMajorant
            v Ωnz pointMajorant) := by
    exact
      SourceClassEndpointMembershipResidualShellShare15.expandedOfFourShareTotal_nonneg_of_pointwiseClassifiedFourMajorant_summandBounds
        (β := β) (H := H) (v := v) (Ω := Ωnz)
        (pointMajorant := pointMajorant)
        (le_of_lt hβpos) (le_of_lt hH)
        hzeroNone htwoNone htwoEndpoint htwoOrigin htwoGhost
        htwoGhostEndpoint htwoGhostOrigin hpoint
  have hrem : 0 < D - paid := lt_of_le_of_lt htotalNonneg hbudget
  simpa [paid, B, Ωnz, D, cap] using hrem

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitStrictMajorantDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitLabelFreePointwiseClassifiedStrictMajorantDenominatorFree
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
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitLabelFreePointwiseClassifiedStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
        ι label := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  rcases hn H hH Ω v hv with
    ⟨zeroNone, twoNone, twoEndpoint, twoOrigin, twoGhost,
      twoGhostEndpoint, twoGhostOrigin, pointMajorant, hzeroNone,
      htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, hpoint, hbudget⟩
  let fourMajorant : Bool → Bool → Bool → ℕ → ℝ :=
    fun hasGhost hasOrigin hasEndpoint k =>
      ∑ R ∈
        finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
          v k,
        ∑ E ∈
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
            v Ωnz hasGhost hasOrigin hasEndpoint R,
          pointMajorant hasGhost hasOrigin hasEndpoint R E
  refine
    ⟨zeroNone, twoNone, twoEndpoint, twoOrigin, twoGhost,
      twoGhostEndpoint, twoGhostOrigin, fourMajorant, hzeroNone,
      htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, ?_, ?_⟩
  · intro hasGhost hasOrigin hasEndpoint k hk
    exact
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_le_classifiedSetPointMajorantSum
        (v := v) (β := β) (H := H) (Ω := Ωnz)
        (ι := ι n v) (label := label Ωnz v)
        (pointMajorant := pointMajorant)
        (hasGhost := hasGhost) (hasOrigin := hasOrigin)
        (hasEndpoint := hasEndpoint) (k := k)
        (hpoint hasGhost hasOrigin hasEndpoint k hk)
  · simpa [fourMajorant, Ωnz] using hbudget

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitStrictMajorantDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitRowStrictMajorantDenominatorFree
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
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitRowStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
        ι label := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  rcases hn H hH Ω v hv with
    ⟨zeroNone, twoNone, twoEndpoint, twoOrigin, twoGhost,
      twoGhostEndpoint, twoGhostOrigin, rowMajorant, hzeroNone,
      htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, hrow, hsum⟩
  let fourMajorant : Bool → Bool → Bool → ℕ → ℝ :=
    fun hasGhost hasOrigin hasEndpoint k =>
      ∑ R ∈
        finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
          v k,
        ∑ i : ι n v hasGhost hasOrigin hasEndpoint R,
          rowMajorant hasGhost hasOrigin hasEndpoint R i
  refine
    ⟨zeroNone, twoNone, twoEndpoint, twoOrigin, twoGhost,
      twoGhostEndpoint, twoGhostOrigin, fourMajorant, hzeroNone,
      htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, ?_, ?_⟩
  · intro hasGhost hasOrigin hasEndpoint k hk
    exact
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_le_rowMajorantSum
        (v := v) (β := β) (H := H) (Ω := Ωnz)
        (ι := ι n v) (label := label Ωnz v)
        (rowMajorant := rowMajorant)
        (hasGhost := hasGhost) (hasOrigin := hasOrigin)
        (hasEndpoint := hasEndpoint) (k := k)
        (hrow hasGhost hasOrigin hasEndpoint k hk)
  · simpa [fourMajorant, Ωnz] using hsum

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitStrictMajorantDenominatorFree
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
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
        ι label := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  rcases hn H hH Ω v hv with
    ⟨zeroNone, twoNone, twoEndpoint, twoOrigin, twoGhost,
      twoGhostEndpoint, twoGhostOrigin, fourMajorant, hzeroNone,
      htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, hfour, hsum⟩
  let shellMajorant :=
    SourceClassEndpointMembershipResidualShellShare15.ofFourShare
      v zeroNone twoNone twoEndpoint twoOrigin twoGhost
      twoGhostEndpoint twoGhostOrigin fourMajorant
  refine ⟨shellMajorant, ?_, ?_⟩
  · exact
      SourceClassEndpointMembershipResidualShellShare15.rawFieldwiseLe_of_fields
        (v := v) (β := β) (H := H) (Ω := Ωnz)
        (zero_none := zeroNone) (two_none := twoNone)
        (two_endpoint := twoEndpoint) (two_origin := twoOrigin)
        (two_ghost := twoGhost)
        (two_ghost_endpoint := twoGhostEndpoint)
        (two_ghost_origin := twoGhostOrigin)
        (fourMajorant := fourMajorant)
        (ι := ι n v) (label := label Ωnz v)
        hzeroNone htwoNone htwoEndpoint htwoOrigin htwoGhost
        htwoGhostEndpoint htwoGhostOrigin hfour
  · simpa [shellMajorant, Ωnz] using hsum

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExpandedStrictMajorantDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellIccExactCardImageExpandedStrictMajorantDenominatorFree
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellIccExactCardImageExpandedStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExpandedStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  rcases hn H hH Ω v hv with
    ⟨zeroNone, twoNone, twoEndpoint, twoOrigin, twoGhost,
      twoGhostEndpoint, twoGhostOrigin, fourMajorant, hzeroNone,
      htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, hfour, hsum⟩
  refine
    ⟨zeroNone, twoNone, twoEndpoint, twoOrigin, twoGhost,
      twoGhostEndpoint, twoGhostOrigin, fourMajorant, hzeroNone,
      htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, ?_, ?_⟩
  · intro hasGhost hasOrigin hasEndpoint k hk
    have hkIcc :
        k ∈
          Finset.Icc
            (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
              hasGhost hasOrigin hasEndpoint)
            ((2 * n + 1) ^ 3 - 2) := by
      simpa [
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_eq_Icc_box_volume_sub_two_of_boundary
          hv hasGhost hasOrigin hasEndpoint] using hk
    rw [
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare_eq_markedResidualExactCardImageSourceClassSum
        β H n Ωnz v hasGhost hasOrigin hasEndpoint k]
    exact hfour hasGhost hasOrigin hasEndpoint k hkIcc
  · simpa [
      Ωnz,
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_eq_Icc_box_volume_sub_two_of_boundary
        hv false false false,
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_eq_Icc_box_volume_sub_two_of_boundary
        hv false false true,
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_eq_Icc_box_volume_sub_two_of_boundary
        hv false true false,
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_eq_Icc_box_volume_sub_two_of_boundary
        hv false true true,
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_eq_Icc_box_volume_sub_two_of_boundary
        hv true false false,
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_eq_Icc_box_volume_sub_two_of_boundary
        hv true false true,
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_eq_Icc_box_volume_sub_two_of_boundary
        hv true true false,
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_eq_Icc_box_volume_sub_two_of_boundary
        hv true true true] using hsum

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExplicitStrictMajorantDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExpandedStrictMajorantDenominatorFree
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExpandedStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExplicitStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  rcases hn H hH Ω v hv with
    ⟨zeroNone, twoNone, twoEndpoint, twoOrigin, twoGhost,
      twoGhostEndpoint, twoGhostOrigin, fourMajorant, hzeroNone,
      htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, hfour, hsum⟩
  refine
    ⟨zeroNone, twoNone, twoEndpoint, twoOrigin, twoGhost,
      twoGhostEndpoint, twoGhostOrigin, fourMajorant, hzeroNone,
      htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, hfour, ?_⟩
  simpa [
    SourceClassEndpointMembershipResidualShellShare15.ofFourShare_total,
    Ωnz] using hsum

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExplicitStrictMajorantDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellIccExactCardImageExpandedStrictMajorantDenominatorFree
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellIccExactCardImageExpandedStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExplicitStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExplicitStrictMajorantDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExpandedStrictMajorantDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExpandedStrictMajorantDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellIccExactCardImageExpandedStrictMajorantDenominatorFree
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExplicitStrictMajorantDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFree
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExplicitStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  rcases hn H hH Ω v hv with ⟨shellMajorant, hfield, hsum⟩
  rcases hfield with
    ⟨hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, hfourNone, hfourEndpoint,
      hfourOrigin, hfourOriginEndpoint, hfourGhost, hfourGhostEndpoint,
      hfourGhostOrigin, hfourGhostOriginEndpoint⟩
  refine
    ⟨shellMajorant.zero_none, shellMajorant.two_none,
      shellMajorant.two_endpoint, shellMajorant.two_origin,
      shellMajorant.two_ghost, shellMajorant.two_ghost_endpoint,
      shellMajorant.two_ghost_origin, shellMajorant.fourShare,
      hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, ?_, ?_⟩
  · intro hasGhost hasOrigin hasEndpoint k hk
    cases hasGhost <;> cases hasOrigin <;> cases hasEndpoint
    · simpa [SourceClassEndpointMembershipResidualShellShare15.fourShare]
        using hfourNone k hk
    · simpa [SourceClassEndpointMembershipResidualShellShare15.fourShare]
        using hfourEndpoint k hk
    · simpa [SourceClassEndpointMembershipResidualShellShare15.fourShare]
        using hfourOrigin k hk
    · simpa [SourceClassEndpointMembershipResidualShellShare15.fourShare]
        using hfourOriginEndpoint k hk
    · simpa [SourceClassEndpointMembershipResidualShellShare15.fourShare]
        using hfourGhost k hk
    · simpa [SourceClassEndpointMembershipResidualShellShare15.fourShare]
        using hfourGhostEndpoint k hk
    · simpa [SourceClassEndpointMembershipResidualShellShare15.fourShare]
        using hfourGhostOrigin k hk
    · simpa [SourceClassEndpointMembershipResidualShellShare15.fourShare]
        using hfourGhostOriginEndpoint k hk
  · have hself :
        SourceClassEndpointMembershipResidualShellShare15.ofFourShare
          v shellMajorant.zero_none shellMajorant.two_none
          shellMajorant.two_endpoint shellMajorant.two_origin
          shellMajorant.two_ghost shellMajorant.two_ghost_endpoint
          shellMajorant.two_ghost_origin shellMajorant.fourShare =
            shellMajorant := by
      cases shellMajorant
      rfl
    simpa [hself, Ωnz] using hsum

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExplicitStrictMajorantDenominatorFree
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExplicitStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  rcases hn H hH Ω v hv with
    ⟨zeroNone, twoNone, twoEndpoint, twoOrigin, twoGhost,
      twoGhostEndpoint, twoGhostOrigin, fourMajorant, hzeroNone,
      htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, hfour, hsum⟩
  let shellMajorant :=
    SourceClassEndpointMembershipResidualShellShare15.ofFourShare
      v zeroNone twoNone twoEndpoint twoOrigin twoGhost
      twoGhostEndpoint twoGhostOrigin fourMajorant
  refine ⟨shellMajorant, ?_, ?_⟩
  · exact
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFieldwiseLe_of_fields
        (v := v) (β := β) (H := H) (Ω := Ωnz)
        (zero_none := zeroNone) (two_none := twoNone)
        (two_endpoint := twoEndpoint) (two_origin := twoOrigin)
        (two_ghost := twoGhost)
        (two_ghost_endpoint := twoGhostEndpoint)
        (two_ghost_origin := twoGhostOrigin)
        (fourMajorant := fourMajorant)
        hzeroNone htwoNone htwoEndpoint htwoOrigin htwoGhost
        htwoGhostEndpoint htwoGhostOrigin hfour
  · simpa [shellMajorant, Ωnz] using hsum

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFree
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
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
        ι label := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  rcases hn H hH Ω v hv with
    ⟨shellMajorant, hrawField, hsum⟩
  refine ⟨shellMajorant.toBudget15, ?_, ?_⟩
  · exact
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15_fieldwiseLe_toBudget15_of_rawFieldwiseLe
        (Sh := shellMajorant) (β := β) (H := H)
        (Ω := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω)
        (ι := ι n v)
        (label := label (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω) v)
        hrawField
  · simpa [SourceClassEndpointMembershipResidualShellShare15.toBudget15_total]
      using hsum

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFree
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  rcases hn H hH Ω v hv with
    ⟨shellMajorant, hrawField, hsum⟩
  refine ⟨shellMajorant.toBudget15, ?_, ?_⟩
  · exact
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawBudget15_fieldwiseLe_toBudget15_of_labelFreeRawFieldwiseLe
        (Sh := shellMajorant) (β := β) (H := H)
        (Ω := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω)
        hrawField
  · simpa [SourceClassEndpointMembershipResidualShellShare15.toBudget15_total]
      using hsum

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFree
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
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
        ι label := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  rcases hn H hH Ω v hv with
    ⟨shellMajorant, hrawField, hsum⟩
  refine ⟨shellMajorant, ?_, ?_⟩
  · exact
      SourceClassEndpointMembershipResidualShellShare15.rawFieldwiseLe_of_labelFreeRawFieldwiseLe
        (Sh := shellMajorant) (β := β) (H := H) (Ω := Ωnz)
        (ι := ι n v) (label := label Ωnz v)
        hrawField
  · simpa [Ωnz] using hsum

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFree
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
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  rcases hn H hH Ω v hv with
    ⟨shellMajorant, hrawField, hsum⟩
  refine ⟨shellMajorant, ?_, ?_⟩
  · exact
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFieldwiseLe_of_rawFieldwiseLe
        (Sh := shellMajorant) (β := β) (H := H) (Ω := Ωnz)
        (ι := ι n v) (label := label Ωnz v)
        hrawField
  · simpa [Ωnz] using hsum

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFreeAbsorption_iff_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFree
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
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
        ι label ↔
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical := by
  constructor
  · exact
      boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFree
  · exact
      boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFree

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFree
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
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
        ι label := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  rcases hn H hH Ω v hv with ⟨B, hfield, hsumB⟩
  refine ⟨B, ?_, ?_⟩
  · have hraw :
        SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15
            v β H Ωnz (ι n v) (label Ωnz v) =
          SourceClassEndpointMembershipResidualShellShare15.labelFreeRawBudget15
            v β H Ωnz := by
      simpa [Ωnz] using
        (SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15_eq_labelFreeRawBudget15
          (v := v) (β := β) (H := H) (Ω := Ωnz)
          (ι := ι n v) (label := label Ωnz v))
    simpa [Ωnz, hraw] using hfield
  · simpa [Ωnz] using hsumB

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFree
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
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  rcases hn H hH Ω v hv with ⟨B, hfield, hsumB⟩
  refine ⟨B, ?_, ?_⟩
  · have hraw :
        SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15
            v β H Ωnz (ι n v) (label Ωnz v) =
          SourceClassEndpointMembershipResidualShellShare15.labelFreeRawBudget15
            v β H Ωnz := by
      simpa [Ωnz] using
        (SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15_eq_labelFreeRawBudget15
          (v := v) (β := β) (H := H) (Ω := Ωnz)
          (ι := ι n v) (label := label Ωnz v))
    simpa [Ωnz, hraw] using hfield
  · simpa [Ωnz] using hsumB

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFreeAbsorption_iff_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFree
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
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
        ι label ↔
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical := by
  constructor
  · exact
      boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFree
  · exact
      boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFree

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFree
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let rawBudget :=
    SourceClassEndpointMembershipResidualShellShare15.labelFreeRawBudget15
      v β H Ωnz
  let rawShell :=
    SourceClassEndpointMembershipResidualShellShare15.labelFreeRawTotal
      v β H Ωnz
  rcases hn H hH Ω v hv with ⟨B, hfield, hsumB⟩
  have hrawLe : rawShell ≤ B.total := by
    calc
      rawShell = rawBudget.total := by
        symm
        simpa [rawBudget, rawShell] using
          SourceClassEndpointMembershipResidualShellShare15.labelFreeRawBudget15_total
            (v := v) (β := β) (H := H) (Ω := Ωnz)
      _ ≤ B.total :=
        SourceClassEndpointMembershipLiveBudget15.total_le_of_fieldwiseLe
          hfield
  have hrawSum :
      cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
              β H n +
          cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
              β H n v +
          finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
            β H n v +
          rawShell < D := by
    linarith
  simpa [rawShell, cap, D, Ωnz] using hrawSum

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedResidualEnvelopeClassifiedCardCanonicalExpandedStrictRemainder
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedResidualEnvelopeClassifiedCardCanonicalExpandedStrictRemainderAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFree
      (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExplicitStrictMajorantDenominatorFree
        (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExplicitStrictMajorantDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExpandedStrictMajorantDenominatorFree
          (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExpandedStrictMajorantDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedResidualEnvelopeClassifiedCardCanonicalExpandedStrictRemainder
            h))))

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedPointwiseClassifiedCanonicalExpandedStrictRemainder
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedPointwiseClassifiedCanonicalExpandedStrictRemainderAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFree
      (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExplicitStrictMajorantDenominatorFree
        (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExplicitStrictMajorantDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExpandedStrictMajorantDenominatorFree
          (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExpandedStrictMajorantDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedPointwiseClassifiedCanonicalExpandedStrictRemainder
            h))))

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictDenominatorFree
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
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorptionPositiveSubcritical
        ι label := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  have hraw :
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawTotal
          v β H Ωnz (ι n v) (label Ωnz v) =
        SourceClassEndpointMembershipResidualShellShare15.labelFreeRawTotal
          v β H Ωnz := by
    simpa [Ωnz] using
      (SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawTotal_eq_labelFreeRawTotal
        (v := v) (β := β) (H := H) (Ω := Ωnz)
        (ι := ι n v) (label := label Ωnz v))
  simpa [Ωnz, hraw] using hn H hH Ω v hv

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictDenominatorFree
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
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  have hraw :
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawTotal
          v β H Ωnz (ι n v) (label Ωnz v) =
        SourceClassEndpointMembershipResidualShellShare15.labelFreeRawTotal
          v β H Ωnz := by
    simpa [Ωnz] using
      (SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawTotal_eq_labelFreeRawTotal
        (v := v) (β := β) (H := H) (Ω := Ωnz)
        (ι := ι n v) (label := label Ωnz v))
  simpa [Ωnz, hraw] using hn H hH Ω v hv

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorption_iff_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictDenominatorFree
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
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorptionPositiveSubcritical
        ι label ↔
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorptionPositiveSubcritical := by
  constructor
  · exact
      boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictDenominatorFree
  · exact
      boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictDenominatorFree

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFree
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
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorptionPositiveSubcritical
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
  rcases hn H hH Ω v hv with ⟨B, hfield, hsumB⟩
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
  have hrawSum :
      cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
              β H n +
          cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
              β H n v +
          finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
            β H n v +
          rawShell < D := by
    linarith
  simpa [rawShell, cap, D, Ωnz] using hrawSum

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictDenominatorFree
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
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical
        ι label := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
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
  let rawShell :=
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawTotal
      v β H Ωnz (ι n v) (label Ωnz v)
  have hsum : paid + rawShell < D := by
    simpa [paid, rawShell, Ωnz, cap, D] using hn H hH Ω v hv
  have hrawNonneg : 0 ≤ rawShell := by
    simpa [rawShell, Ωnz] using
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawTotal_nonneg
        (v := v) (β := β) (H := H) (Ω := Ωnz)
        (ι := ι n v) (label := label Ωnz v)
        (le_of_lt hβpos) (le_of_lt hH)
  have hrawR : rawShell < R := by
    dsimp [R]
    linarith
  have hRpos : 0 < R := by
    linarith
  exact ⟨hRpos, hrawR⟩

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictShare
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
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorptionPositiveSubcritical
        ι label := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
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
  let rawShell :=
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawTotal
      v β H Ωnz (ι n v) (label Ωnz v)
  rcases hn H hH Ω v hv with ⟨_hRpos, hrawR⟩
  have hsum : paid + rawShell < D := by
    linarith
  simpa [paid, rawShell, Ωnz, cap, D] using hsum

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorption_iff_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictShare
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
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorptionPositiveSubcritical
        ι label ↔
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical
        ι label :=
  ⟨boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictDenominatorFree,
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictShare⟩

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedResidualEnvelopeClassifiedCardCanonicalExpandedStrictRemainder
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
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedResidualEnvelopeClassifiedCardCanonicalExpandedStrictRemainderAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical
        ι label :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictDenominatorFree
    (ι := ι) (label := label)
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictDenominatorFree
      (ι := ι) (label := label)
      (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedResidualEnvelopeClassifiedCardCanonicalExpandedStrictRemainder
        h))

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedPointwiseClassifiedCanonicalExpandedStrictRemainder
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
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedPointwiseClassifiedCanonicalExpandedStrictRemainderAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical
        ι label :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictDenominatorFree
    (ι := ι) (label := label)
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictDenominatorFree
      (ι := ι) (label := label)
      (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedPointwiseClassifiedCanonicalExpandedStrictRemainder
        h))

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorption_of_boundaryCrossingRemainderPositive_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderDenominatorFree
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
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderDenominatorFreeAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical
        ι label := by
  intro β hβpos hβc
  filter_upwards [hpos β hβpos hβc, hraw β hβpos hβc] with
    n hnpos hnraw
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
  let rawShell :=
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawTotal
      v β H Ωnz (ι n v) (label Ωnz v)
  have hRpos : 0 < R := by
    simpa [R, paid, Ωnz, cap, D] using hnpos H hH Ω v hv
  have hrawR : rawShell ≤ R := by
    simpa [R, paid, rawShell, Ωnz, cap, D] using hnraw H hH Ω v hv
  exact ⟨hRpos, hrawR⟩

end Exact3D
end StatMech
