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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part53
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.residualEnvelopeClassifiedCardFourMajorant_nonneg
    {n : ℕ} {v : FK.boxVerts 3 n}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {residualEnvelope :
      Bool → Bool → Bool → Finset (Option (FK.boxVerts 3 n)) → ℝ}
    {hasGhost hasOrigin hasEndpoint : Bool} {k : ℕ}
    (henv :
      ∀ R,
        R ∈
            finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
              v k →
          0 ≤ residualEnvelope hasGhost hasOrigin hasEndpoint R) :
    0 ≤
      SourceClassEndpointMembershipResidualShellShare15.residualEnvelopeClassifiedCardFourMajorant
        v Ω residualEnvelope hasGhost hasOrigin hasEndpoint k := by
  unfold SourceClassEndpointMembershipResidualShellShare15.residualEnvelopeClassifiedCardFourMajorant
  exact
    Finset.sum_nonneg fun R hR =>
      mul_nonneg (Nat.cast_nonneg _) (henv R hR)

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.residualEnvelopeClassifiedCardFourMajorant_nonneg_of_summandBounds
    {β H : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H)
    {n : ℕ} {v : FK.boxVerts 3 n}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {residualEnvelope :
      Bool → Bool → Bool → Finset (Option (FK.boxVerts 3 n)) → ℝ}
    {hasGhost hasOrigin hasEndpoint : Bool} {k : ℕ}
    (henv :
      ∀ R,
        R ∈
            finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
              v k →
          ∀ E,
            E ∈
                finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
                  v Ω hasGhost hasOrigin hasEndpoint R →
              finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                  β H E ≤
                residualEnvelope hasGhost hasOrigin hasEndpoint R) :
    0 ≤
      SourceClassEndpointMembershipResidualShellShare15.residualEnvelopeClassifiedCardFourMajorant
        v Ω residualEnvelope hasGhost hasOrigin hasEndpoint k := by
  classical
  unfold SourceClassEndpointMembershipResidualShellShare15.residualEnvelopeClassifiedCardFourMajorant
  refine Finset.sum_nonneg ?_
  intro R hR
  let C :=
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
      v Ω hasGhost hasOrigin hasEndpoint R
  by_cases hC0 : C.card = 0
  · simp [C, hC0]
  · have hCpos : 0 < C.card := Nat.pos_of_ne_zero hC0
    rcases Finset.card_pos.mp hCpos with ⟨E, hE⟩
    have henvNonneg :
        0 ≤ residualEnvelope hasGhost hasOrigin hasEndpoint R :=
      le_trans
        (finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand_nonneg
          hβ hH E)
        (henv R hR E (by simpa [C] using hE))
    exact mul_nonneg (Nat.cast_nonneg _) henvNonneg

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.residualEnvelopeClassifiedCardFourMajorant_mono
    {n : ℕ} {v : FK.boxVerts 3 n}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {residualEnvelopeA residualEnvelopeB :
      Bool → Bool → Bool → Finset (Option (FK.boxVerts 3 n)) → ℝ}
    {hasGhost hasOrigin hasEndpoint : Bool} {k : ℕ}
    (henv :
      ∀ R,
        R ∈
            finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
              v k →
          residualEnvelopeA hasGhost hasOrigin hasEndpoint R ≤
            residualEnvelopeB hasGhost hasOrigin hasEndpoint R) :
    SourceClassEndpointMembershipResidualShellShare15.residualEnvelopeClassifiedCardFourMajorant
        v Ω residualEnvelopeA hasGhost hasOrigin hasEndpoint k ≤
      SourceClassEndpointMembershipResidualShellShare15.residualEnvelopeClassifiedCardFourMajorant
        v Ω residualEnvelopeB hasGhost hasOrigin hasEndpoint k := by
  unfold SourceClassEndpointMembershipResidualShellShare15.residualEnvelopeClassifiedCardFourMajorant
  exact
    Finset.sum_le_sum fun R hR =>
      mul_le_mul_of_nonneg_left (henv R hR) (Nat.cast_nonneg _)

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.pointwiseClassifiedFourMajorant_nonneg
    {n : ℕ} {v : FK.boxVerts 3 n}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {pointMajorant :
      ∀ (_ : Bool) (_ : Bool) (_ : Bool)
        (_ : Finset (Option (FK.boxVerts 3 n))),
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ℝ}
    {hasGhost hasOrigin hasEndpoint : Bool} {k : ℕ}
    (hpoint :
      ∀ R,
        R ∈
            finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
              v k →
          ∀ E,
            E ∈
                finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
                  v Ω hasGhost hasOrigin hasEndpoint R →
              0 ≤ pointMajorant hasGhost hasOrigin hasEndpoint R E) :
    0 ≤
      SourceClassEndpointMembershipResidualShellShare15.pointwiseClassifiedFourMajorant
        v Ω pointMajorant hasGhost hasOrigin hasEndpoint k := by
  unfold SourceClassEndpointMembershipResidualShellShare15.pointwiseClassifiedFourMajorant
  exact
    Finset.sum_nonneg fun R hR =>
      Finset.sum_nonneg fun E hE => hpoint R hR E hE

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.pointwiseClassifiedFourMajorant_nonneg_of_summandBounds
    {β H : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H)
    {n : ℕ} {v : FK.boxVerts 3 n}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {pointMajorant :
      ∀ (_ : Bool) (_ : Bool) (_ : Bool)
        (_ : Finset (Option (FK.boxVerts 3 n))),
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ℝ}
    {hasGhost hasOrigin hasEndpoint : Bool} {k : ℕ}
    (hpoint :
      ∀ R,
        R ∈
            finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
              v k →
          ∀ E,
            E ∈
                finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
                  v Ω hasGhost hasOrigin hasEndpoint R →
              finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                  β H E ≤
                pointMajorant hasGhost hasOrigin hasEndpoint R E) :
    0 ≤
      SourceClassEndpointMembershipResidualShellShare15.pointwiseClassifiedFourMajorant
        v Ω pointMajorant hasGhost hasOrigin hasEndpoint k := by
  classical
  unfold SourceClassEndpointMembershipResidualShellShare15.pointwiseClassifiedFourMajorant
  exact
    Finset.sum_nonneg fun R hR =>
      Finset.sum_nonneg fun E hE =>
        le_trans
          (finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand_nonneg
            hβ hH E)
          (hpoint R hR E hE)

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.pointwiseClassifiedFourMajorant_mono
    {n : ℕ} {v : FK.boxVerts 3 n}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {pointMajorantA pointMajorantB :
      ∀ (_ : Bool) (_ : Bool) (_ : Bool)
        (_ : Finset (Option (FK.boxVerts 3 n))),
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ℝ}
    {hasGhost hasOrigin hasEndpoint : Bool} {k : ℕ}
    (hpoint :
      ∀ R,
        R ∈
            finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
              v k →
          ∀ E,
            E ∈
                finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
                  v Ω hasGhost hasOrigin hasEndpoint R →
              pointMajorantA hasGhost hasOrigin hasEndpoint R E ≤
                pointMajorantB hasGhost hasOrigin hasEndpoint R E) :
    SourceClassEndpointMembershipResidualShellShare15.pointwiseClassifiedFourMajorant
        v Ω pointMajorantA hasGhost hasOrigin hasEndpoint k ≤
      SourceClassEndpointMembershipResidualShellShare15.pointwiseClassifiedFourMajorant
        v Ω pointMajorantB hasGhost hasOrigin hasEndpoint k := by
  unfold SourceClassEndpointMembershipResidualShellShare15.pointwiseClassifiedFourMajorant
  exact
    Finset.sum_le_sum fun R hR =>
      Finset.sum_le_sum fun E hE => hpoint R hR E hE

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_eq_labelFreeRawFourShare
    {β H : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool}
    {ι :
      Bool → Bool → Bool →
        Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ hasGhost hasOrigin hasEndpoint R,
      Fintype (ι hasGhost hasOrigin hasEndpoint R)]
    [∀ hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ hasGhost hasOrigin hasEndpoint R,
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ι hasGhost hasOrigin hasEndpoint R}
    {k : ℕ} :
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
        v β H Ω ι label hasGhost hasOrigin hasEndpoint k =
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
        v β H Ω hasGhost hasOrigin hasEndpoint k := by
  simpa [
    SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare] using
    (SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_eq_classifiedSetSum
      (v := v) (β := β) (H := H) (Ω := Ω)
      (ι := ι) (label := label) (hasGhost := hasGhost)
      (hasOrigin := hasOrigin) (hasEndpoint := hasEndpoint) (k := k))

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_eq_zero_of_boundary_of_threshold_add_k_odd
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool)
    {ι :
      Bool → Bool → Bool →
        Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ hasGhost hasOrigin hasEndpoint R,
      Fintype (ι hasGhost hasOrigin hasEndpoint R)]
    [∀ hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι hasGhost hasOrigin hasEndpoint R)]
    (label :
      ∀ hasGhost hasOrigin hasEndpoint R,
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ι hasGhost hasOrigin hasEndpoint R)
    {k : ℕ}
    (hodd :
      Odd
        (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
            hasGhost hasOrigin hasEndpoint +
          k)) :
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
        v β H Ω ι label hasGhost hasOrigin hasEndpoint k =
      0 := by
  rw [
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_eq_labelFreeRawFourShare]
  exact
    SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare_eq_zero_of_boundary_of_threshold_add_k_odd
      β H n Ω hv hasGhost hasOrigin hasEndpoint hodd

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_le_classifiedSetPointMajorantSum
    {β H : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool}
    {ι :
      Bool → Bool → Bool →
        Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ hasGhost hasOrigin hasEndpoint R,
      Fintype (ι hasGhost hasOrigin hasEndpoint R)]
    [∀ hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ hasGhost hasOrigin hasEndpoint R,
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ι hasGhost hasOrigin hasEndpoint R}
    {pointMajorant :
      ∀ _ _ _ (_ : Finset (Option (FK.boxVerts 3 n))),
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ℝ}
    {k : ℕ}
    (hpoint :
      ∀ R,
        R ∈
            finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
              v k →
          ∀ E,
            E ∈
                finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
                  v Ω hasGhost hasOrigin hasEndpoint R →
              finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                  β H E ≤
                pointMajorant hasGhost hasOrigin hasEndpoint R E) :
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
        v β H Ω ι label hasGhost hasOrigin hasEndpoint k ≤
      ∑ R ∈
        finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
          v k,
        ∑ E ∈
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
            v Ω hasGhost hasOrigin hasEndpoint R,
          pointMajorant hasGhost hasOrigin hasEndpoint R E := by
  classical
  rw [
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_eq_classifiedSetSum
      (v := v) (β := β) (H := H) (Ω := Ω)
      (ι := ι) (label := label) (hasGhost := hasGhost)
      (hasOrigin := hasOrigin) (hasEndpoint := hasEndpoint) (k := k)]
  exact
    Finset.sum_le_sum fun R hR =>
      Finset.sum_le_sum fun E hE => hpoint R hR E hE

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare_le_classifiedSetPointMajorantSum
    {β H : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool}
    {pointMajorant :
      ∀ _ _ _ (_ : Finset (Option (FK.boxVerts 3 n))),
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ℝ}
    {k : ℕ}
    (hpoint :
      ∀ R,
        R ∈
            finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
              v k →
          ∀ E,
            E ∈
                finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
                  v Ω hasGhost hasOrigin hasEndpoint R →
              finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                  β H E ≤
                pointMajorant hasGhost hasOrigin hasEndpoint R E) :
    SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
        v β H Ω hasGhost hasOrigin hasEndpoint k ≤
      ∑ R ∈
        finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
          v k,
        ∑ E ∈
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
            v Ω hasGhost hasOrigin hasEndpoint R,
          pointMajorant hasGhost hasOrigin hasEndpoint R E := by
  classical
  unfold SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
  exact
    Finset.sum_le_sum fun R hR =>
      Finset.sum_le_sum fun E hE => hpoint R hR E hE

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare_le_pointwiseClassifiedFourMajorant
    {β H : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool}
    {pointMajorant :
      ∀ _ _ _ (_ : Finset (Option (FK.boxVerts 3 n))),
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ℝ}
    {k : ℕ}
    (hpoint :
      ∀ R,
        R ∈
            finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
              v k →
          ∀ E,
            E ∈
                finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
                  v Ω hasGhost hasOrigin hasEndpoint R →
              finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                  β H E ≤
                pointMajorant hasGhost hasOrigin hasEndpoint R E) :
    SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
        v β H Ω hasGhost hasOrigin hasEndpoint k ≤
      SourceClassEndpointMembershipResidualShellShare15.pointwiseClassifiedFourMajorant
        v Ω pointMajorant hasGhost hasOrigin hasEndpoint k := by
  simpa [
    SourceClassEndpointMembershipResidualShellShare15.pointwiseClassifiedFourMajorant]
    using
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare_le_classifiedSetPointMajorantSum
        (v := v) (β := β) (H := H) (Ω := Ω)
        (pointMajorant := pointMajorant)
        (hasGhost := hasGhost) (hasOrigin := hasOrigin)
        (hasEndpoint := hasEndpoint) (k := k) hpoint

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_le_rowMajorantSum
    {β H : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool}
    {ι :
      Bool → Bool → Bool →
        Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ hasGhost hasOrigin hasEndpoint R,
      Fintype (ι hasGhost hasOrigin hasEndpoint R)]
    [∀ hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ hasGhost hasOrigin hasEndpoint R,
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ι hasGhost hasOrigin hasEndpoint R}
    {rowMajorant :
      ∀ hasGhost hasOrigin hasEndpoint
        (R : Finset (Option (FK.boxVerts 3 n))),
        ι hasGhost hasOrigin hasEndpoint R → ℝ}
    {k : ℕ}
    (hrow :
      ∀ R,
        R ∈
            finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
              v k →
          ∀ i : ι hasGhost hasOrigin hasEndpoint R,
            (∑ E ∈
              finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
                v Ω hasGhost hasOrigin hasEndpoint R
                (label hasGhost hasOrigin hasEndpoint R) i,
              finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                β H E) ≤
              rowMajorant hasGhost hasOrigin hasEndpoint R i) :
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
        v β H Ω ι label hasGhost hasOrigin hasEndpoint k ≤
      ∑ R ∈
        finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
          v k,
        ∑ i : ι hasGhost hasOrigin hasEndpoint R,
          rowMajorant hasGhost hasOrigin hasEndpoint R i := by
  classical
  unfold SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
  exact
    Finset.sum_le_sum fun R hR =>
      Finset.sum_le_sum fun i _hi => hrow R hR i

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_le_pointMajorantSum
    {β H : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool}
    {ι :
      Bool → Bool → Bool →
        Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ hasGhost hasOrigin hasEndpoint R,
      Fintype (ι hasGhost hasOrigin hasEndpoint R)]
    [∀ hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ hasGhost hasOrigin hasEndpoint R,
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ι hasGhost hasOrigin hasEndpoint R}
    {pointMajorant :
      ∀ hasGhost hasOrigin hasEndpoint
        (R : Finset (Option (FK.boxVerts 3 n))),
        ι hasGhost hasOrigin hasEndpoint R →
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ℝ}
    {k : ℕ}
    (hpoint :
      ∀ R,
        R ∈
            finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
              v k →
          ∀ i : ι hasGhost hasOrigin hasEndpoint R,
            ∀ E,
              E ∈
                  finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
                    v Ω hasGhost hasOrigin hasEndpoint R
                    (label hasGhost hasOrigin hasEndpoint R) i →
                finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                    β H E ≤
                  pointMajorant hasGhost hasOrigin hasEndpoint R i E) :
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
        v β H Ω ι label hasGhost hasOrigin hasEndpoint k ≤
      ∑ R ∈
        finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
          v k,
        ∑ i : ι hasGhost hasOrigin hasEndpoint R,
          ∑ E ∈
            finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
              v Ω hasGhost hasOrigin hasEndpoint R
              (label hasGhost hasOrigin hasEndpoint R) i,
            pointMajorant hasGhost hasOrigin hasEndpoint R i E := by
  classical
  unfold SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
  exact
    Finset.sum_le_sum fun R hR =>
      Finset.sum_le_sum fun i _hi =>
        Finset.sum_le_sum fun E hE => hpoint R hR i E hE

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_le_rowEnvelopeCardSum
    {β H : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool}
    {ι :
      Bool → Bool → Bool →
        Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ hasGhost hasOrigin hasEndpoint R,
      Fintype (ι hasGhost hasOrigin hasEndpoint R)]
    [∀ hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ hasGhost hasOrigin hasEndpoint R,
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ι hasGhost hasOrigin hasEndpoint R}
    {rowEnvelope :
      ∀ hasGhost hasOrigin hasEndpoint
        (R : Finset (Option (FK.boxVerts 3 n))),
        ι hasGhost hasOrigin hasEndpoint R → ℝ}
    {k : ℕ}
    (henv :
      ∀ R,
        R ∈
            finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
              v k →
          ∀ i : ι hasGhost hasOrigin hasEndpoint R,
            ∀ E,
              E ∈
                  finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
                    v Ω hasGhost hasOrigin hasEndpoint R
                    (label hasGhost hasOrigin hasEndpoint R) i →
                finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                    β H E ≤
                  rowEnvelope hasGhost hasOrigin hasEndpoint R i) :
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
        v β H Ω ι label hasGhost hasOrigin hasEndpoint k ≤
      ∑ R ∈
        finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
          v k,
        ∑ i : ι hasGhost hasOrigin hasEndpoint R,
          ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
              v Ω hasGhost hasOrigin hasEndpoint R
              (label hasGhost hasOrigin hasEndpoint R) i).card : ℝ) *
            rowEnvelope hasGhost hasOrigin hasEndpoint R i := by
  classical
  unfold SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
  exact
    Finset.sum_le_sum fun R hR =>
      Finset.sum_le_sum fun i _hi => by
        have hsum :
            (∑ E ∈
              finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
                v Ω hasGhost hasOrigin hasEndpoint R
                (label hasGhost hasOrigin hasEndpoint R) i,
              finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                β H E) ≤
              ∑ E ∈
                finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
                  v Ω hasGhost hasOrigin hasEndpoint R
                  (label hasGhost hasOrigin hasEndpoint R) i,
                rowEnvelope hasGhost hasOrigin hasEndpoint R i := by
          exact Finset.sum_le_sum fun E hE => henv R hR i E hE
        simpa [Finset.sum_const, nsmul_eq_mul] using hsum

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_le_rowEnvelopeCardMajorantSum
    {β H : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool}
    {ι :
      Bool → Bool → Bool →
        Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ hasGhost hasOrigin hasEndpoint R,
      Fintype (ι hasGhost hasOrigin hasEndpoint R)]
    [∀ hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ hasGhost hasOrigin hasEndpoint R,
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ι hasGhost hasOrigin hasEndpoint R}
    {rowEnvelope cardMajorant :
      ∀ hasGhost hasOrigin hasEndpoint
        (R : Finset (Option (FK.boxVerts 3 n))),
        ι hasGhost hasOrigin hasEndpoint R → ℝ}
    {k : ℕ}
    (henv :
      ∀ R,
        R ∈
            finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
              v k →
          ∀ i : ι hasGhost hasOrigin hasEndpoint R,
            ∀ E,
              E ∈
                  finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
                    v Ω hasGhost hasOrigin hasEndpoint R
                    (label hasGhost hasOrigin hasEndpoint R) i →
                finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                    β H E ≤
                  rowEnvelope hasGhost hasOrigin hasEndpoint R i)
    (hcard :
      ∀ R,
        R ∈
            finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
              v k →
          ∀ i : ι hasGhost hasOrigin hasEndpoint R,
            ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
                v Ω hasGhost hasOrigin hasEndpoint R
                (label hasGhost hasOrigin hasEndpoint R) i).card : ℝ) ≤
              cardMajorant hasGhost hasOrigin hasEndpoint R i)
    (henv_nonneg :
      ∀ R,
        R ∈
            finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
              v k →
          ∀ i : ι hasGhost hasOrigin hasEndpoint R,
            0 ≤ rowEnvelope hasGhost hasOrigin hasEndpoint R i) :
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
        v β H Ω ι label hasGhost hasOrigin hasEndpoint k ≤
      ∑ R ∈
        finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
          v k,
        ∑ i : ι hasGhost hasOrigin hasEndpoint R,
          cardMajorant hasGhost hasOrigin hasEndpoint R i *
            rowEnvelope hasGhost hasOrigin hasEndpoint R i := by
  classical
  unfold SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
  exact
    Finset.sum_le_sum fun R hR =>
      Finset.sum_le_sum fun i _hi => by
        have hsum :
            (∑ E ∈
              finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
                v Ω hasGhost hasOrigin hasEndpoint R
                (label hasGhost hasOrigin hasEndpoint R) i,
              finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                β H E) ≤
              ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
                  v Ω hasGhost hasOrigin hasEndpoint R
                  (label hasGhost hasOrigin hasEndpoint R) i).card : ℝ) *
                rowEnvelope hasGhost hasOrigin hasEndpoint R i := by
          have hsum' :
              (∑ E ∈
                finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
                  v Ω hasGhost hasOrigin hasEndpoint R
                  (label hasGhost hasOrigin hasEndpoint R) i,
                finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                  β H E) ≤
                ∑ E ∈
                  finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
                    v Ω hasGhost hasOrigin hasEndpoint R
                    (label hasGhost hasOrigin hasEndpoint R) i,
                  rowEnvelope hasGhost hasOrigin hasEndpoint R i := by
            exact Finset.sum_le_sum fun E hE => henv R hR i E hE
          simpa [Finset.sum_const, nsmul_eq_mul] using hsum'
        exact
          le_trans hsum
            (mul_le_mul_of_nonneg_right (hcard R hR i)
              (henv_nonneg R hR i))

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_le_rowEnvelopeClassifiedCardSum
    {β H : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool}
    {ι :
      Bool → Bool → Bool →
        Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ hasGhost hasOrigin hasEndpoint R,
      Fintype (ι hasGhost hasOrigin hasEndpoint R)]
    [∀ hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ hasGhost hasOrigin hasEndpoint R,
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ι hasGhost hasOrigin hasEndpoint R}
    {rowEnvelope :
      ∀ hasGhost hasOrigin hasEndpoint
        (R : Finset (Option (FK.boxVerts 3 n))),
        ι hasGhost hasOrigin hasEndpoint R → ℝ}
    {k : ℕ}
    (henv :
      ∀ R,
        R ∈
            finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
              v k →
          ∀ i : ι hasGhost hasOrigin hasEndpoint R,
            ∀ E,
              E ∈
                  finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
                    v Ω hasGhost hasOrigin hasEndpoint R
                    (label hasGhost hasOrigin hasEndpoint R) i →
                finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                    β H E ≤
                  rowEnvelope hasGhost hasOrigin hasEndpoint R i)
    (henv_nonneg :
      ∀ R,
        R ∈
            finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
              v k →
          ∀ i : ι hasGhost hasOrigin hasEndpoint R,
            0 ≤ rowEnvelope hasGhost hasOrigin hasEndpoint R i) :
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
        v β H Ω ι label hasGhost hasOrigin hasEndpoint k ≤
      ∑ R ∈
        finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
          v k,
        ∑ i : ι hasGhost hasOrigin hasEndpoint R,
          ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
              v Ω hasGhost hasOrigin hasEndpoint R).card : ℝ) *
            rowEnvelope hasGhost hasOrigin hasEndpoint R i := by
  classical
  exact
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_le_rowEnvelopeCardMajorantSum
      (v := v) (β := β) (H := H) (Ω := Ω)
      (ι := ι) (label := label) (rowEnvelope := rowEnvelope)
      (cardMajorant := fun hasGhost hasOrigin hasEndpoint R _i =>
        ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
          v Ω hasGhost hasOrigin hasEndpoint R).card : ℝ))
      (hasGhost := hasGhost) (hasOrigin := hasOrigin)
      (hasEndpoint := hasEndpoint) (k := k)
      henv
      (fun R _hR i =>
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet_card_le_classifiedSet_card
          v Ω hasGhost hasOrigin hasEndpoint R
          (label hasGhost hasOrigin hasEndpoint R) i)
      henv_nonneg

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_le_residualEnvelopeClassifiedCardSum
    {β H : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool}
    {ι :
      Bool → Bool → Bool →
        Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ hasGhost hasOrigin hasEndpoint R,
      Fintype (ι hasGhost hasOrigin hasEndpoint R)]
    [∀ hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ hasGhost hasOrigin hasEndpoint R,
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ι hasGhost hasOrigin hasEndpoint R}
    {residualEnvelope :
      ∀ _ _ _ (_ : Finset (Option (FK.boxVerts 3 n))), ℝ}
    {k : ℕ}
    (henv :
      ∀ R,
        R ∈
            finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
              v k →
          ∀ E,
            E ∈
                finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
                  v Ω hasGhost hasOrigin hasEndpoint R →
              finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                  β H E ≤
                residualEnvelope hasGhost hasOrigin hasEndpoint R) :
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
        v β H Ω ι label hasGhost hasOrigin hasEndpoint k ≤
      ∑ R ∈
        finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
          v k,
        ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
            v Ω hasGhost hasOrigin hasEndpoint R).card : ℝ) *
          residualEnvelope hasGhost hasOrigin hasEndpoint R := by
  classical
  rw [
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_eq_classifiedSetSum
      (v := v) (β := β) (H := H) (Ω := Ω)
      (ι := ι) (label := label) (hasGhost := hasGhost)
      (hasOrigin := hasOrigin) (hasEndpoint := hasEndpoint) (k := k)]
  exact
    Finset.sum_le_sum fun R hR => by
      have hsum :
          (∑ E ∈
            finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
              v Ω hasGhost hasOrigin hasEndpoint R,
            finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
              β H E) ≤
            ∑ E ∈
              finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
                v Ω hasGhost hasOrigin hasEndpoint R,
              residualEnvelope hasGhost hasOrigin hasEndpoint R := by
        exact
          Finset.sum_le_sum fun E hE => henv R hR E hE
      simpa [Finset.sum_const, nsmul_eq_mul] using hsum

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare_le_residualEnvelopeClassifiedCardSum
    {β H : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool}
    {residualEnvelope :
      ∀ _ _ _ (_ : Finset (Option (FK.boxVerts 3 n))), ℝ}
    {k : ℕ}
    (henv :
      ∀ R,
        R ∈
            finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
              v k →
          ∀ E,
            E ∈
                finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
                  v Ω hasGhost hasOrigin hasEndpoint R →
              finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                  β H E ≤
                residualEnvelope hasGhost hasOrigin hasEndpoint R) :
    SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
        v β H Ω hasGhost hasOrigin hasEndpoint k ≤
      ∑ R ∈
        finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
          v k,
        ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
            v Ω hasGhost hasOrigin hasEndpoint R).card : ℝ) *
          residualEnvelope hasGhost hasOrigin hasEndpoint R := by
  classical
  unfold SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
  exact
    Finset.sum_le_sum fun R hR => by
      have hsum :
          (∑ E ∈
            finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
              v Ω hasGhost hasOrigin hasEndpoint R,
            finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
              β H E) ≤
            ∑ E ∈
              finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
                v Ω hasGhost hasOrigin hasEndpoint R,
              residualEnvelope hasGhost hasOrigin hasEndpoint R := by
        exact Finset.sum_le_sum fun E hE => henv R hR E hE
      simpa [Finset.sum_const, nsmul_eq_mul] using hsum

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare_le_residualEnvelopeClassifiedCardFourMajorant
    {β H : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool}
    {residualEnvelope :
      ∀ _ _ _ (_ : Finset (Option (FK.boxVerts 3 n))), ℝ}
    {k : ℕ}
    (henv :
      ∀ R,
        R ∈
            finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
              v k →
          ∀ E,
            E ∈
                finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
                  v Ω hasGhost hasOrigin hasEndpoint R →
              finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                  β H E ≤
                residualEnvelope hasGhost hasOrigin hasEndpoint R) :
    SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
        v β H Ω hasGhost hasOrigin hasEndpoint k ≤
      SourceClassEndpointMembershipResidualShellShare15.residualEnvelopeClassifiedCardFourMajorant
        v Ω residualEnvelope hasGhost hasOrigin hasEndpoint k := by
  simpa [
    SourceClassEndpointMembershipResidualShellShare15.residualEnvelopeClassifiedCardFourMajorant]
    using
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare_le_residualEnvelopeClassifiedCardSum
        (v := v) (β := β) (H := H) (Ω := Ω)
        (residualEnvelope := residualEnvelope)
        (hasGhost := hasGhost) (hasOrigin := hasOrigin)
        (hasEndpoint := hasEndpoint) (k := k) henv

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_eq_supportResidualExactCardSourceClassSum_of_boundary_of_mem_shellIndex
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    {ι :
      Bool → Bool → Bool →
        Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ hasGhost hasOrigin hasEndpoint R,
      Fintype (ι hasGhost hasOrigin hasEndpoint R)]
    [∀ hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι hasGhost hasOrigin hasEndpoint R)]
    (label :
      ∀ hasGhost hasOrigin hasEndpoint R,
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ι hasGhost hasOrigin hasEndpoint R)
    (hasGhost hasOrigin hasEndpoint : Bool) {k : ℕ}
    (hk :
      k ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v hasGhost hasOrigin hasEndpoint) :
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
        v β H Ω ι label hasGhost hasOrigin hasEndpoint k =
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum
        β H n Ω v hasGhost hasOrigin hasEndpoint k := by
  classical
  rw [
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum_eq_unmarkedResidualCard_sum_of_boundary_of_mem_shellIndex
      β H n Ω v hv hasGhost hasOrigin hasEndpoint hk]
  unfold SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
  apply Finset.sum_congr rfl
  intro R _hR
  rw [
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseSourceClassSum_eq_label_sum
      β H n Ω v hasGhost hasOrigin hasEndpoint R
      (label hasGhost hasOrigin hasEndpoint R)]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSum_eq_sum_labelSet
      v β H Ω hasGhost hasOrigin hasEndpoint R
      (label hasGhost hasOrigin hasEndpoint R) i]

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_shellSum_eq_markedResidualThresholdShellImageSourceClassSum_of_boundary
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    {ι :
      Bool → Bool → Bool →
        Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ hasGhost hasOrigin hasEndpoint R,
      Fintype (ι hasGhost hasOrigin hasEndpoint R)]
    [∀ hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι hasGhost hasOrigin hasEndpoint R)]
    (label :
      ∀ hasGhost hasOrigin hasEndpoint R,
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ι hasGhost hasOrigin hasEndpoint R)
    (hasGhost hasOrigin hasEndpoint : Bool) :
    (∑ k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v hasGhost hasOrigin hasEndpoint,
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
        v β H Ω ι label hasGhost hasOrigin hasEndpoint k) =
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
        β H n Ω v hasGhost hasOrigin hasEndpoint := by
  classical
  unfold finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
  apply Finset.sum_congr rfl
  intro k hk
  have hsupport :
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
          v β H Ω ι label hasGhost hasOrigin hasEndpoint k =
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum
          β H n Ω v hasGhost hasOrigin hasEndpoint k :=
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_eq_supportResidualExactCardSourceClassSum_of_boundary_of_mem_shellIndex
      β H n Ω v hv label hasGhost hasOrigin hasEndpoint hk
  have himage :
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
          β H n Ω v hasGhost hasOrigin hasEndpoint k =
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum
          β H n Ω v hasGhost hasOrigin hasEndpoint k := by
    simpa [
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum,
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet]
      using
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum_eq_sourceClassSupport_endpointMembership_fourPlus_unmarkedResidualCard_sum_of_boundary_of_mem_shellIndex
          β H n Ω v hv hasGhost hasOrigin hasEndpoint hk
  exact hsupport.trans himage.symm

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.normalizedRows_fourShare_mul_eq_rawFourShare
    {β H D : ℝ} (hDne : D ≠ 0) {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {ι :
      Bool → Bool → Bool →
        Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ hasGhost hasOrigin hasEndpoint R,
      Fintype (ι hasGhost hasOrigin hasEndpoint R)]
    [∀ hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ hasGhost hasOrigin hasEndpoint R,
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ι hasGhost hasOrigin hasEndpoint R}
    (hasGhost hasOrigin hasEndpoint : Bool) (k : ℕ) :
    (SourceClassEndpointMembershipResidualShellShare15.normalizedRows
        v β H D Ω ι label).fourShare hasGhost hasOrigin hasEndpoint k *
        D =
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
        v β H Ω ι label hasGhost hasOrigin hasEndpoint k := by
  rw [
    SourceClassEndpointMembershipResidualShellShare15.normalizedRows_fourShare
      (v := v) (β := β) (H := H) (D := D) (Ω := Ω)
      (ι := ι) (label := label) hasGhost hasOrigin hasEndpoint k]
  unfold SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
  simp_rw [← Finset.sum_div]
  exact div_mul_cancel₀ _ hDne

end Exact3D
end StatMech
