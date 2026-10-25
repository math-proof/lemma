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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part134
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentShareAbsorption_of_positiveDenominatorComponentSum
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientPositiveDenominatorComponentSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentShareAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let oneTerm :=
    cap * finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm β H n
  let boundaryTerm :=
    cap *
      finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm β H n v
  let emptyTerm :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let coefficientTerm :=
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
      β H n Ωnz v
  rcases hn H hH Ω v hv with ⟨hDpos, hsum⟩
  have hD : 0 ≤ D := le_of_lt hDpos
  have hcap : 0 ≤ cap := by
    simpa [cap, boundaryCrossingCap] using
      finiteBoundaryGhostCollapsedCutoffBoundaryFiberBoundaryCrossingPairCountMultiplicityCap_nonneg
        Ωnz
  have honeFactor :
      0 ≤ finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
        β H n :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm_nonneg
      (le_of_lt hβpos) (le_of_lt hH)
  have hboundaryFactor :
      0 ≤ finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
        β H n v :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm_nonneg
      (le_of_lt hβpos) (le_of_lt hH) v
  have honeTerm : 0 ≤ oneTerm := by
    exact mul_nonneg hcap honeFactor
  have hboundaryTerm : 0 ≤ boundaryTerm := by
    exact mul_nonneg hcap hboundaryFactor
  have hemptyTerm : 0 ≤ emptyTerm := by
    simpa [emptyTerm] using
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm_nonneg
        (le_of_lt hβpos) (le_of_lt hH) v
  have hcoefficientTerm : 0 ≤ coefficientTerm := by
    simpa [coefficientTerm] using
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum_nonneg
        (le_of_lt hβpos) (le_of_lt hH) n Ωnz v
  have hsum' : oneTerm + boundaryTerm + emptyTerm + coefficientTerm ≤ D := by
    simpa [oneTerm, boundaryTerm, emptyTerm, coefficientTerm, cap, D, Ωnz]
      using hsum
  rcases
    fourShares_of_nonneg_sum_le hD honeTerm hboundaryTerm hemptyTerm
      hcoefficientTerm hsum' with
    ⟨oneShare, boundaryPairShare, emptyBoundaryShare, coefficientShare,
      honeShare, hboundaryShare, hemptyShare, hcoefficientShare, hshareSum,
      hone, hboundary, hempty, hcoefficient⟩
  exact
    ⟨oneShare, boundaryPairShare, emptyBoundaryShare, coefficientShare,
      honeShare, hboundaryShare, hemptyShare, hcoefficientShare, hshareSum,
      by simpa [oneTerm, cap, D] using hone,
      by simpa [boundaryTerm, cap, D] using hboundary,
      by simpa [emptyTerm, D] using hempty,
      by simpa [coefficientTerm, D] using hcoefficient⟩

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientPositiveDenominatorComponentSumAbsorption_of_boundaryVertexDenominatorPositive_componentSum
    (hpos :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositivePositiveSubcritical)
    (hsum :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientPositiveDenominatorComponentSumAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hpos β hβpos hβc, hsum β hβpos hβc] with
    n hnpos hnsum
  intro H hH Ω v hv
  exact ⟨hnpos H hH v hv, hnsum H hH Ω v hv⟩

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientPositiveDenominatorComponentSumAbsorption_of_boundaryVertexDenominatorPositiveCurrentWitness_componentSum
    (hpos :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositiveCurrentWitnessPositiveSubcritical)
    (hsum :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientPositiveDenominatorComponentSumAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientPositiveDenominatorComponentSumAbsorption_of_boundaryVertexDenominatorPositive_componentSum
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositive_of_boundaryVertexDenominatorPositiveCurrentWitness
      hpos)
    hsum

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientPositiveDenominatorComponentSumAbsorption_of_boundaryVertexDenominatorPositiveSupportCurrentWitness_componentSum
    (hpos :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositiveSupportCurrentWitnessPositiveSubcritical)
    (hsum :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientPositiveDenominatorComponentSumAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientPositiveDenominatorComponentSumAbsorption_of_boundaryVertexDenominatorPositive_componentSum
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositive_of_boundaryVertexDenominatorPositiveSupportCurrentWitness
      hpos)
    hsum

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientPositiveDenominatorComponentSumAbsorption_of_originalPathWitness3D_componentSum
    (hpath : FiniteBoundaryGhostOriginalPathWitness3D)
    (hsum :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientPositiveDenominatorComponentSumAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientPositiveDenominatorComponentSumAbsorption_of_boundaryVertexDenominatorPositiveSupportCurrentWitness_componentSum
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositiveSupportCurrentWitness_of_originalPathWitness3D
      hpath)
    hsum

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorption_of_componentShare
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  rcases hn H hH Ω v hv with
    ⟨oneShare, boundaryPairShare, emptyBoundaryShare, coefficientShare,
      _honeShare, _hboundaryShare, _hemptyShare, _hcoefficientShare,
      hshareSum, hone, hboundary, hempty, hcoefficient⟩
  have hD : 0 ≤ D := by
    dsimp [D]
    exact finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct_nonneg
      (β := β) (H := H) (n := n) (le_of_lt hβpos) (le_of_lt hH) v
  calc
    cap *
          finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
            β H n +
        cap *
          finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
            β H n v +
        finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v +
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
          β H n Ωnz v
        ≤
          oneShare * D + boundaryPairShare * D +
            emptyBoundaryShare * D + coefficientShare * D := by
          exact
            add_le_add (add_le_add (add_le_add hone hboundary) hempty)
              hcoefficient
    _ =
        (oneShare + boundaryPairShare + emptyBoundaryShare +
            coefficientShare) * D := by
      ring
    _ ≤ 1 * D := mul_le_mul_of_nonneg_right hshareSum hD
    _ =
        finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v := by
      simp [D]

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_componentSum
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  have hsum :
      cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
              β H n +
          cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
              β H n v +
          finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v +
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
            β H n Ωnz v ≤
        finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v := by
    simpa [Ωnz, cap] using hn H hH Ω v hv
  have hcap :
      finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ωnz v ≤ cap := by
    have hcardCross :
        finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ωnz v ≤
          finiteBoundaryGhostCollapsedCutoffBoundaryFiberCrossingPairCap
            n Ωnz :=
      finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard_le_crossingPairCap
        Ωnz v
    have hcrossSource :
        finiteBoundaryGhostCollapsedCutoffBoundaryFiberCrossingPairCap n Ωnz ≤
          finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap
            n Ωnz :=
      finiteBoundaryGhostCollapsedCutoffBoundaryFiberCrossingPairCap_le_sourceSectorMultiplicityCap
        Ωnz
    have hsourceBoundary :
        finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap
            n Ωnz ≤
          boundaryCrossingCap n Ωnz := by
      simpa [Ωnz, boundaryCrossingCap] using
        finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap_le_boundaryCrossingPairCountMultiplicityCap_weightNonzeroCutoff
          (β := β) (H := H) Ω
    exact hcardCross.trans (hcrossSource.trans hsourceBoundary)
  have hmain :
      0 ≤ finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm_nonneg
      (β := β) (H := H) (n := n) (le_of_lt hβpos) (le_of_lt hH) v
  have hprofile :
      finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ωnz v ≤
        cap * finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
            β H n +
          cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
              β H n v +
          finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v := by
    calc
      finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ωnz v =
          finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ωnz v *
              finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v +
            finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v :=
        finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile_eq_card_mul_main_add_empty
          β H n Ωnz v
      _ ≤
          cap *
              finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v +
            finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v := by
        exact add_le_add (mul_le_mul_of_nonneg_right hcap hmain) le_rfl
      _ =
          cap * finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
              β H n +
            cap *
              finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                β H n v +
            finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v := by
        rw [
          finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm_eq_onePoint_add_boundaryPair]
        ring
  rw [
    finiteBoundaryGhostBoundaryFiberSourcePairVertexProfileWithNonTwoPointClassifiedCoefficient]
  calc
    finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ωnz v +
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
          β H n Ωnz v
        ≤
          (cap * finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
              β H n +
            cap *
              finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                β H n v +
            finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v) +
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
            β H n Ωnz v := by
          exact add_le_add hprofile le_rfl
    _ =
        cap * finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
            β H n +
          cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
              β H n v +
          finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v +
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
            β H n Ωnz v := by
      ring
    _ ≤ finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v :=
      hsum

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_componentShare
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_componentSum
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorption_of_componentShare
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_positiveDenominatorComponentSum
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientPositiveDenominatorComponentSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_componentShare
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentShareAbsorption_of_positiveDenominatorComponentSum
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_coefficientLabelComponentSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ι}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientLabelComponentSumAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_componentSum
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorption_of_coefficientLabelComponentSum
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_dependentCoefficientLabelComponentSum
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ι n}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientDependentLabelComponentSumAbsorptionPositiveSubcritical
        ι label) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_componentSum
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorption_of_dependentCoefficientLabelComponentSum
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_sourceClassComponentSum
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassComponentSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_dependentCoefficientLabelComponentSum
    h

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_sourceClassSupportComponentSum
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportComponentSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_componentSum
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorption_of_sourceClassSupportComponentSum
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_sourceClassSupportComponentShare
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportComponentShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_sourceClassSupportComponentSum
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportComponentSumAbsorption_of_componentShare
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_sourceClassSupportPositiveDenominatorComponentSum
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportPositiveDenominatorComponentSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_sourceClassSupportComponentShare
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportComponentShareAbsorption_of_positiveDenominatorComponentSum
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_sourceClassSupportGhostMembershipComponentSum
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportGhostMembershipComponentSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_componentSum
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorption_of_sourceClassSupportGhostMembershipComponentSum
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_sourceClassSupportGhostMembershipComponentShare
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportGhostMembershipComponentShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_sourceClassSupportGhostMembershipComponentSum
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportGhostMembershipComponentSumAbsorption_of_componentShare
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_sourceClassSupportCardinalityComponentSum
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportCardinalityComponentSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_componentSum
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorption_of_sourceClassSupportCardinalityComponentSum
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_sourceClassSupportEndpointMembershipComponentSum
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportEndpointMembershipComponentSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_componentSum
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorption_of_sourceClassSupportEndpointMembershipComponentSum
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_sourceClassSupportLiveEndpointMembershipComponentSum
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportLiveEndpointMembershipComponentSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_sourceClassSupportEndpointMembershipComponentSum
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportEndpointMembershipComponentSumAbsorption_of_liveEndpointMembershipComponentSum
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_sourceClassSupportExplicitLiveEndpointMembershipComponentSum
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportExplicitLiveEndpointMembershipComponentSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_sourceClassSupportLiveEndpointMembershipComponentSum
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportLiveEndpointMembershipComponentSumAbsorption_of_explicitLiveEndpointMembershipComponentSum
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_sourceClassSupportExplicitLiveEndpointMembershipBudget15ComponentSum
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportExplicitLiveEndpointMembershipBudget15ComponentSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_sourceClassSupportExplicitLiveEndpointMembershipComponentSum
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportExplicitLiveEndpointMembershipComponentSumAbsorption_of_budget15
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_sourceClassSupportResidualBudget15ComponentSum
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualBudget15ComponentSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_sourceClassSupportExplicitLiveEndpointMembershipBudget15ComponentSum
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportExplicitLiveEndpointMembershipBudget15ComponentSumAbsorption_of_residualBudget15
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_sourceClassSupportResidualThresholdBudget15ComponentShare
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdBudget15ComponentShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_sourceClassSupportResidualBudget15ComponentSum
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualBudget15ComponentSumAbsorption_of_residualThresholdBudget15ComponentShare
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_sourceClassSupportResidualThresholdShellBudget15ComponentShare
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_sourceClassSupportResidualThresholdBudget15ComponentShare
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdBudget15ComponentShareAbsorption_of_residualThresholdShellBudget15ComponentShare
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_sourceClassSupportResidualThresholdExactCardShellBudget15ComponentShare
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdExactCardShellBudget15ComponentShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_sourceClassSupportResidualThresholdShellBudget15ComponentShare
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentShareAbsorption_of_residualThresholdExactCardShellBudget15ComponentShare
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_sourceClassSupportResidualThresholdSupportExactCardShellBudget15ComponentShare
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardShellBudget15ComponentShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_sourceClassSupportResidualThresholdExactCardShellBudget15ComponentShare
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdExactCardShellBudget15ComponentShareAbsorption_of_residualThresholdSupportExactCardShellBudget15ComponentShare
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_sourceClassSupportResidualThresholdSupportExactCardDependentLabelBudget15ComponentShare
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
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_sourceClassSupportResidualThresholdSupportExactCardShellBudget15ComponentShare
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardShellBudget15ComponentShareAbsorption_of_dependentLabelBudget15ComponentShare
      h)

set_option linter.style.longLine false in


theorem
    boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceNonTwoPointClassifiedCoefficientProfileMajorization_absorption
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationWithNonTwoPointClassifiedCoefficientPositiveSubcritical)
    (hsource :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hmajor β hβpos hβc, hsource β hβpos hβc] with
    n hnmajor hnsource
  intro H hH Ω v hv
  exact (hnmajor H hH Ω v hv).trans (hnsource H hH Ω v hv)

set_option linter.style.longLine false in


theorem
    boundaryVertexDecrementedSourceAbsorption_of_nonTwoPointClassifiedCoefficientProfileAbsorption
    (hsource :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical :=
  boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceNonTwoPointClassifiedCoefficientProfileMajorization_absorption
    boundaryVertexDecrementedSourceProfileMajorizationWithNonTwoPointClassifiedCoefficient
    hsource

set_option linter.style.longLine false in


theorem finiteCutoffBound_of_nonTwoPointClassifiedCoefficientProfileAbsorption
    (hsource :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_decrementedSourceAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorption_of_boundaryVertexDecrementedSourceAbsorption
      (boundaryVertexDecrementedSourceAbsorption_of_nonTwoPointClassifiedCoefficientProfileAbsorption
        hsource))

set_option linter.style.longLine false in


theorem firstExitPositive_of_nonTwoPointClassifiedCoefficientProfileAbsorption
    (hsource :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_decrementedSourceAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorption_of_boundaryVertexDecrementedSourceAbsorption
      (boundaryVertexDecrementedSourceAbsorption_of_nonTwoPointClassifiedCoefficientProfileAbsorption
        hsource))

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientProfileAbsorption
    (hsource :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_decrementedSourceAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorption_of_boundaryVertexDecrementedSourceAbsorption
      (boundaryVertexDecrementedSourceAbsorption_of_nonTwoPointClassifiedCoefficientProfileAbsorption
        hsource))

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientComponentSumAbsorption
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentSumAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientProfileAbsorption
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_componentSum
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientComponentShareAbsorption
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientComponentShareAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientProfileAbsorption
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_componentShare
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientPositiveDenominatorComponentSumAbsorption
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientPositiveDenominatorComponentSumAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientProfileAbsorption
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_positiveDenominatorComponentSum
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientLabelComponentSumAbsorption
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ι}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientLabelComponentSumAbsorptionPositiveSubcritical
        ι label) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientProfileAbsorption
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_coefficientLabelComponentSum
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientDependentLabelComponentSumAbsorption
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ι n}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientDependentLabelComponentSumAbsorptionPositiveSubcritical
        ι label) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientProfileAbsorption
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_dependentCoefficientLabelComponentSum
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassComponentSumAbsorption
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassComponentSumAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientDependentLabelComponentSumAbsorption
    h

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportComponentSumAbsorption
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportComponentSumAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientProfileAbsorption
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_sourceClassSupportComponentSum
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportComponentShareAbsorption
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportComponentShareAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientProfileAbsorption
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_sourceClassSupportComponentShare
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportPositiveDenominatorComponentSumAbsorption
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportPositiveDenominatorComponentSumAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientProfileAbsorption
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_sourceClassSupportPositiveDenominatorComponentSum
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportGhostMembershipComponentSumAbsorption
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportGhostMembershipComponentSumAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientProfileAbsorption
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_sourceClassSupportGhostMembershipComponentSum
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportGhostMembershipComponentShareAbsorption
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportGhostMembershipComponentShareAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientProfileAbsorption
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_sourceClassSupportGhostMembershipComponentShare
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportCardinalityComponentSumAbsorption
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportCardinalityComponentSumAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientProfileAbsorption
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_sourceClassSupportCardinalityComponentSum
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportEndpointMembershipComponentSumAbsorption
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportEndpointMembershipComponentSumAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientProfileAbsorption
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientAbsorption_of_sourceClassSupportEndpointMembershipComponentSum
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportLiveEndpointMembershipComponentSumAbsorption
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportLiveEndpointMembershipComponentSumAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportEndpointMembershipComponentSumAbsorption
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportEndpointMembershipComponentSumAbsorption_of_liveEndpointMembershipComponentSum
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportExplicitLiveEndpointMembershipComponentSumAbsorption
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportExplicitLiveEndpointMembershipComponentSumAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportLiveEndpointMembershipComponentSumAbsorption
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportLiveEndpointMembershipComponentSumAbsorption_of_explicitLiveEndpointMembershipComponentSum
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportExplicitLiveEndpointMembershipBudget15ComponentSumAbsorption
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportExplicitLiveEndpointMembershipBudget15ComponentSumAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportExplicitLiveEndpointMembershipComponentSumAbsorption
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportExplicitLiveEndpointMembershipComponentSumAbsorption_of_budget15
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualBudget15ComponentSumAbsorption
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualBudget15ComponentSumAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportExplicitLiveEndpointMembershipBudget15ComponentSumAbsorption
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportExplicitLiveEndpointMembershipBudget15ComponentSumAbsorption_of_residualBudget15
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdBudget15ComponentShareAbsorption
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdBudget15ComponentShareAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualBudget15ComponentSumAbsorption
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualBudget15ComponentSumAbsorption_of_residualThresholdBudget15ComponentShare
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentShareAbsorption
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentShareAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdBudget15ComponentShareAbsorption
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdBudget15ComponentShareAbsorption_of_residualThresholdShellBudget15ComponentShare
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdExactCardShellBudget15ComponentShareAbsorption
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdExactCardShellBudget15ComponentShareAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentShareAbsorption
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentShareAbsorption_of_residualThresholdExactCardShellBudget15ComponentShare
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardShellBudget15ComponentShareAbsorption
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardShellBudget15ComponentShareAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdExactCardShellBudget15ComponentShareAbsorption
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdExactCardShellBudget15ComponentShareAbsorption_of_residualThresholdSupportExactCardShellBudget15ComponentShare
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardResidualCaseBudget15ComponentShareAbsorption
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardResidualCaseBudget15ComponentShareAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardShellBudget15ComponentShareAbsorption
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardShellBudget15ComponentShareAbsorption_of_residualThresholdSupportExactCardResidualCaseBudget15ComponentShare
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardDependentLabelBudget15ComponentShareAbsorption
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
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardResidualCaseBudget15ComponentShareAbsorption
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardResidualCaseBudget15ComponentShareAbsorption_of_dependentLabelBudget15ComponentShare
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardPointwiseDependentLabelBudget15ComponentShareAbsorption
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
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardDependentLabelBudget15ComponentShareAbsorption
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardDependentLabelBudget15ComponentShareAbsorption_of_pointwiseDependentLabelBudget15ComponentShare
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardNormalizedRowDependentLabelBudget15ComponentShareAbsorption
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
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardPointwiseDependentLabelBudget15ComponentShareAbsorption
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardPointwiseDependentLabelBudget15ComponentShareAbsorption_of_normalizedRowDependentLabelBudget15ComponentShare
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15ComponentShareAbsorption
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
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardNormalizedRowDependentLabelBudget15ComponentShareAbsorption
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardNormalizedRowDependentLabelBudget15ComponentShareAbsorption_of_canonicalNormalizedRowDependentLabelBudget15ComponentShare
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15ComponentSumAbsorption
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
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15ComponentShareAbsorption
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15ComponentShareAbsorption_of_canonicalNormalizedRowDependentLabelBudget15ComponentSum
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentSumAbsorption
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
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15ComponentSumAbsorption
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15ComponentSumAbsorption_of_canonicalRawRowDependentLabelBudget15ComponentSum
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentMajorantSumAbsorption
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
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentSumAbsorption
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentSumAbsorption_of_canonicalRawRowDependentLabelBudget15ComponentMajorantSum
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSumAbsorption
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
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentSumAbsorption
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentSumAbsorption_of_boxGeometry_canonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSum
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeMajorantSumAbsorption
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
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeMajorantSumAbsorptionPositiveSubcritical
        ι label) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentMajorantSumAbsorption
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentMajorantSumAbsorption_of_boxGeometry_canonicalRawRowDependentLabelBudget15ComponentDenominatorFreeMajorantSum
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentDenominatorFreeSumAbsorption
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical := by
  let ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type :=
    fun _n _v _hasGhost _hasOrigin _hasEndpoint _R => Unit
  let label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R :=
    fun {_n} _Ω _v _hasGhost _hasOrigin _hasEndpoint _R _E =>
      ()
  exact
    boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeMajorantSumAbsorption
      (ι := ι) (label := label)
      (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeMajorantSumAbsorption_of_residualThresholdShellBudget15ComponentDenominatorFreeSum
        (ι := ι) (label := label) h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareAbsorption
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentDenominatorFreeSumAbsorption
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentDenominatorFreeSumAbsorption_of_aggregateComponentShare
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleAbsorption
    {oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare :
      ResidualThresholdShellBudget15AggregateShareSchedule}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleAbsorptionPositiveSubcritical
        oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareAbsorption
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareAbsorption_of_shareSchedule
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleComponents
    {oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare :
      ResidualThresholdShellBudget15AggregateShareSchedule}
    (hbudget :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleBudgetPositiveSubcritical
        oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare)
    (hone :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleOnePointPositiveSubcritical
        oneShare)
    (hboundary :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleBoundaryPairPositiveSubcritical
        boundaryPairShare)
    (hempty :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleEmptyBoundaryPositiveSubcritical
        emptyBoundaryShare)
    (hshell :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleShellBudgetPositiveSubcritical
        shellBudgetShare) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleAbsorption
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleAbsorption_of_components
      hbudget hone hboundary hempty hshell)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15CanonicalRatioShareSum
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15CanonicalRatioShareSumPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleAbsorption
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleAbsorption_of_canonicalRatioShareSum
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictCanonicalRatioShareSum
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictCanonicalRatioShareSumPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15CanonicalRatioShareSum
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15CanonicalRatioShareSum_of_strictCanonicalRatioShareSum
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictAggregateComponentShare
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictAggregateComponentShareAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictCanonicalRatioShareSum
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictCanonicalRatioShareSum_of_strictAggregateComponentShare
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictAggregateComponentShareScheduleAbsorption
    {oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare :
      ResidualThresholdShellBudget15AggregateShareSchedule}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictAggregateComponentShareScheduleAbsorptionPositiveSubcritical
        oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictAggregateComponentShare
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictAggregateComponentShareAbsorption_of_strictShareSchedule
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictAggregateComponentShareScheduleComponents
    {oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare :
      ResidualThresholdShellBudget15AggregateShareSchedule}
    (hbudget :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictAggregateComponentShareScheduleBudgetPositiveSubcritical
        oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare)
    (hone :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleOnePointPositiveSubcritical
        oneShare)
    (hboundary :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleBoundaryPairPositiveSubcritical
        boundaryPairShare)
    (hempty :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleEmptyBoundaryPositiveSubcritical
        emptyBoundaryShare)
    (hshell :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleShellBudgetPositiveSubcritical
        shellBudgetShare) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictAggregateComponentShareScheduleAbsorption
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictAggregateComponentShareScheduleAbsorption_of_components
      hbudget hone hboundary hempty hshell)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShare
    (hpos :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictCanonicalRatioShareSum
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictCanonicalRatioShareSum_of_boundaryCrossingRemainderPositive_strictRemainderShare
      hpos hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareSchedule
    {sectorShare :
      ResidualThresholdShellBudget15BoundaryCrossingRemainderShareSchedule}
    (hpos :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareScheduleAbsorptionPositiveSubcritical
        sectorShare) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShare
    hpos
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_strictShareSchedule
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareComponentStrictCanonicalRatioShareSum
    (hstrict :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictCanonicalRatioShareSum
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictCanonicalRatioShareSum_of_boundaryCrossingCapComponentStrictCanonicalRatioShareSum_strictRemainderShare
      hstrict hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareScheduleComponentStrictCanonicalRatioShareSum
    {sectorShare :
      ResidualThresholdShellBudget15BoundaryCrossingRemainderShareSchedule}
    (hstrict :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareScheduleAbsorptionPositiveSubcritical
        sectorShare) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareComponentStrictCanonicalRatioShareSum
    hstrict
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_strictShareSchedule
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainder
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15CanonicalRatioShareSum
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15CanonicalRatioShareSum_of_boundaryCrossingRemainder
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrict
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareSchedule
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositive_of_boundaryCrossingRemainderStrict
      h)
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareScheduleAbsorption_of_boundaryCrossingRemainderStrict
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictComponentDenominatorFreeSumAbsorption
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictComponentDenominatorFreeSumAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrict
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictAbsorption_of_strictComponentDenominatorFreeSum
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShare
    (hcomponent :
      BoundaryCrossingCapComponentSumPositiveSubcritical)
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainder
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderAbsorption_of_boundaryCrossingCapComponentSum_remainderShare
      hcomponent hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareSchedule
    {sectorShare :
      ResidualThresholdShellBudget15BoundaryCrossingRemainderShareSchedule}
    (hcomponent :
      BoundaryCrossingCapComponentSumPositiveSubcritical)
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareScheduleAbsorptionPositiveSubcritical
        sectorShare) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShare
    hcomponent
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareAbsorption_of_shareSchedule
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareRemainderPositive
    (hremainderPositive :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainder
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderAbsorption_of_boundaryCrossingRemainderPositive_remainderShare
      hremainderPositive hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareScheduleRemainderPositive
    {sectorShare :
      ResidualThresholdShellBudget15BoundaryCrossingRemainderShareSchedule}
    (hremainderPositive :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareScheduleAbsorptionPositiveSubcritical
        sectorShare) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareRemainderPositive
    hremainderPositive
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareAbsorption_of_shareSchedule
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareComponentStrictSum
    (hstrict :
      BoundaryCrossingCapComponentStrictSumPositiveSubcritical)
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareRemainderPositive
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositive_of_boundaryCrossingCapComponentStrictSum
      hstrict)
    hshare

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareComponentStrictShare
    (hstrictShare :
      BoundaryCrossingCapComponentStrictSharePositiveSubcritical)
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareComponentStrictSum
    (boundaryCrossingCapComponentStrictSumAbsorption_of_componentStrictShare
      hstrictShare)
    hshare

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareComponentStrictCanonicalRatioShareSum
    (hstrict :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareComponentStrictShare
    (boundaryCrossingCapComponentStrictShareAbsorption_of_canonicalRatioShareSum
      hstrict)
    hshare

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareScheduleComponentStrictCanonicalRatioShareSum
    {sectorShare :
      ResidualThresholdShellBudget15BoundaryCrossingRemainderShareSchedule}
    (hstrict :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareScheduleAbsorptionPositiveSubcritical
        sectorShare) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareComponentStrictCanonicalRatioShareSum
    hstrict
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareAbsorption_of_shareSchedule
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdExactCardShellBudget15BoundaryCrossingRemainderShare
    (hcomponent :
      BoundaryCrossingCapComponentSumPositiveSubcritical)
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdExactCardShellBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShare
    hcomponent
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareAbsorption_of_residualThresholdExactCardShellBudget15BoundaryCrossingRemainderShare
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdExactCardShellBudget15BoundaryCrossingRemainderStrictShare
    (hpos :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdExactCardShellBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShare
    hpos
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_residualThresholdExactCardShellBudget15BoundaryCrossingRemainderStrictShare
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardShellBudget15BoundaryCrossingRemainderShare
    (hcomponent :
      BoundaryCrossingCapComponentSumPositiveSubcritical)
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardShellBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdExactCardShellBudget15BoundaryCrossingRemainderShare
    hcomponent
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdExactCardShellBudget15BoundaryCrossingRemainderShareAbsorption_of_residualThresholdSupportExactCardShellBudget15BoundaryCrossingRemainderShare
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardShellBudget15BoundaryCrossingRemainderStrictShare
    (hpos :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardShellBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdExactCardShellBudget15BoundaryCrossingRemainderStrictShare
    hpos
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdExactCardShellBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_residualThresholdSupportExactCardShellBudget15BoundaryCrossingRemainderStrictShare
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardDependentLabelBudget15BoundaryCrossingRemainderShare
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
    (hcomponent :
      BoundaryCrossingCapComponentSumPositiveSubcritical)
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardDependentLabelBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical
        ι label) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardShellBudget15BoundaryCrossingRemainderShare
    hcomponent
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardShellBudget15BoundaryCrossingRemainderShareAbsorption_of_dependentLabelBudget15BoundaryCrossingRemainderShare
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardDependentLabelBudget15BoundaryCrossingRemainderStrictShare
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
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical
        ι label) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShare
    hpos
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_dependentLabelBudget15BoundaryCrossingRemainderStrictShare
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardPointwiseDependentLabelBudget15BoundaryCrossingRemainderStrictShare
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
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardPointwiseDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical
        ι label) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShare
    hpos
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_pointwiseDependentLabelBudget15BoundaryCrossingRemainderStrictShare
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15BoundaryCrossingRemainderStrictShare
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
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical
        ι label) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardPointwiseDependentLabelBudget15BoundaryCrossingRemainderStrictShare
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositive_of_canonicalNormalizedRowDependentLabelBudget15BoundaryCrossingRemainderStrictShare
      hshare)
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardPointwiseDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_canonicalNormalizedRowDependentLabelBudget15BoundaryCrossingRemainderStrictShare
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictShare
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
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical
        ι label) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardPointwiseDependentLabelBudget15BoundaryCrossingRemainderStrictShare
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositive_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictShare
      hshare)
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardPointwiseDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictShare
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictDenominatorFree
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
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorptionPositiveSubcritical
        ι label) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictShare
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictDenominatorFree
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictDenominatorFree
    (ι := fun _ _ _ _ _ _ => Unit)
    (label := fun {_n} _Ω _v _hasGhost _hasOrigin _hasEndpoint _R _E => ())
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFree
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExplicitStrictMajorantDenominatorFree
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExplicitStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFree
      (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExplicitStrictMajorantDenominatorFree
        hshare))

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExpandedStrictMajorantDenominatorFree
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExpandedStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExplicitStrictMajorantDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExplicitStrictMajorantDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExpandedStrictMajorantDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellIccExactCardImageExpandedStrictMajorantDenominatorFree
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellIccExactCardImageExpandedStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExpandedStrictMajorantDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExpandedStrictMajorantDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellIccExactCardImageExpandedStrictMajorantDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageExpandedStrictMajorantDenominatorFree
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageExpandedStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellIccExactCardImageExpandedStrictMajorantDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellIccExactCardImageExpandedStrictMajorantDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageExpandedStrictMajorantDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalStrictDenominatorFree
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalStrictDenominatorFreeAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageExpandedStrictMajorantDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageExpandedStrictMajorantDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalStrictDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalStrictRemainderDenominatorFree
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalStrictDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalStrictDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalStrictRemainderDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointStrictRemainderDenominatorFree
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalStrictRemainderDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointStrictRemainderDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneTailStrictRemainderDenominatorFree
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointStrictRemainderDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneTailStrictRemainderDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneResidualSetTailStrictRemainderDenominatorFree
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneResidualSetTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneTailStrictRemainderDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneResidualSetTailStrictRemainderDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonBudgetTailStrictRemainderDenominatorFree
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonBudgetTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneResidualSetTailStrictRemainderDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneResidualSetTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonBudgetTailStrictRemainderDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetTailStrictRemainderDenominatorFree
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneTailStrictRemainderDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTailStrictRemainderDenominatorFree
      (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetTailStrictRemainderDenominatorFree
        hshare))

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTailStrictRemainderDenominatorFree
    {budget : LiveSingletonOptionComponentBudgetSchedule}
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical
        budget) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetTailStrictRemainderDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetTailStrictRemainderDenominatorFreeAbsorption_of_componentBudgetSchedule
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleComponentsTailStrictRemainderDenominatorFree
    {budget : LiveSingletonOptionComponentBudgetSchedule}
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleRemainingPositiveSubcritical
        budget)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTailPositiveSubcritical
        budget)
    (hsingleton :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleSingletonPositiveSubcritical
        budget)
    (hpayment :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetSchedulePaymentPositiveSubcritical
        budget) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTailStrictRemainderDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTailStrictRemainderDenominatorFreeAbsorption_of_components
      hremaining htail hsingleton hpayment)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleResidualCaseSingletonTailStrictRemainderDenominatorFree
    {budget : LiveSingletonOptionComponentBudgetSchedule}
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleRemainingPositiveSubcritical
        budget)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTailPositiveSubcritical
        budget)
    (hpayment :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetSchedulePaymentPositiveSubcritical
        budget)
    (hsingletonResidual :
      ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
        ∀ᶠ n in atTop,
          ∀ H : ℝ, 0 < H →
            ∀ Ω : Finset
              (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
              ∀ v, ∀ _hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
                let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
                let liveOptions :=
                  finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
                    v Ωnz true true true
                ∀ x ∈ liveOptions,
                  ∃ share D : ℝ,
                    SourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare
                      v β H Ωnz true true true
                      ({x} : Finset (Option (FK.boxVerts 3 n))) share D ∧
                    share * D ≤ budget.singletonBudget β H Ωnz v x) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleComponentsTailStrictRemainderDenominatorFree
    hremaining htail
    (liveSingletonOptionComponentBudgetScheduleSingleton_of_residualCaseShareBudget
      hsingletonResidual)
    hpayment

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleNamedResidualCaseSingletonTailStrictRemainderDenominatorFree
    {budget : LiveSingletonOptionComponentBudgetSchedule}
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleRemainingPositiveSubcritical
        budget)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTailPositiveSubcritical
        budget)
    (hpayment :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetSchedulePaymentPositiveSubcritical
        budget)
    (hsingletonResidual :
      LiveSingletonOptionComponentBudgetScheduleResidualCaseShareBudgetPositiveSubcritical
        budget) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleResidualCaseSingletonTailStrictRemainderDenominatorFree
    hremaining htail hpayment hsingletonResidual

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTailStrictRemainderDenominatorFree
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneTailStrictRemainderDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTailStrictRemainderDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareTailStrictRemainderDenominatorFree
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneTailStrictRemainderDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareTailStrictRemainderDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFree
    {schedule : LiveSingletonOptionShareSchedule}
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical
        schedule) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareTailStrictRemainderDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareTailStrictRemainderDenominatorFreeAbsorption_of_shareSchedule
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleDerivedSignTailStrictRemainderDenominatorFree
    {schedule : LiveSingletonOptionShareSchedule}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        schedule)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        schedule)
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical
        schedule)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical
        schedule)
    (hsingleton :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleSingletonPositiveSubcritical
        schedule) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorption_of_derivedSignComponents
      hR hstrict hremaining htail hsingleton)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseSingletonDerivedSignTailStrictRemainderDenominatorFree
    {schedule : LiveSingletonOptionShareSchedule}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        schedule)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        schedule)
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical
        schedule)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical
        schedule)
    (hsingletonResidual :
      LiveSingletonOptionShareScheduleResidualCaseSingletonDenominatorNonnegativePayment
        schedule) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorption_of_residualCaseSingletonDerivedSignComponents
      hR hstrict hremaining htail hsingletonResidual)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseSingletonPaymentDerivedSignTailStrictRemainderDenominatorFree
    {schedule : LiveSingletonOptionShareSchedule}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        schedule)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        schedule)
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical
        schedule)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical
        schedule)
    (hsingletonResidual :
      LiveSingletonOptionShareScheduleResidualCaseSingletonPayment
        schedule) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorption_of_residualCaseSingletonPaymentDerivedSignComponents
      hR hstrict hremaining htail hsingletonResidual)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsDerivedSignTailStrictRemainderDenominatorFree
    {schedule : LiveSingletonOptionShareSchedule}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        schedule)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        schedule)
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical
        schedule)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical
        schedule)
    (hpayment :
      ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
        ∀ᶠ n in atTop,
          ∀ H : ℝ, 0 < H →
            ∀ Ω : Finset
              (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
              ∀ v, ∀ _hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
                let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
                let cap := boundaryCrossingCap n Ωnz
                let D :=
                  finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct
                    β H n v
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
                let liveOptions :=
                  finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
                    v Ωnz true true true
                ∀ x ∈ liveOptions,
                  (∑ E ∈
                    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
                      v Ωnz true true true
                      ({x} : Finset (Option (FK.boxVerts 3 n))),
                    finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                      β H E / R) ≤
                    schedule.singletonShare β H Ωnz v x) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleDerivedSignTailStrictRemainderDenominatorFree
    hR hstrict hremaining htail
    (liveSingletonOptionShareScheduleSingleton_of_residualCaseNormalizedPointwiseRows
      hR hpayment)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsDerivedSignTailStrictRemainderDenominatorFreeRemainderPositive
    {schedule : LiveSingletonOptionShareSchedule}
    (hpos :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        schedule)
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical
        schedule)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical
        schedule)
    (hpayment :
      ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
        ∀ᶠ n in atTop,
          ∀ H : ℝ, 0 < H →
            ∀ Ω : Finset
              (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
              ∀ v, ∀ _hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
                let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
                let cap := boundaryCrossingCap n Ωnz
                let D :=
                  finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct
                    β H n v
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
                let liveOptions :=
                  finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
                    v Ωnz true true true
                ∀ x ∈ liveOptions,
                  (∑ E ∈
                    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
                      v Ωnz true true true
                      ({x} : Finset (Option (FK.boxVerts 3 n))),
                    finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                      β H E / R) ≤
                    schedule.singletonShare β H Ωnz v x) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsDerivedSignTailStrictRemainderDenominatorFree
    (schedule := schedule)
    (liveSingletonOptionShareScheduleRemainderPositive_of_boundaryCrossingRemainderPositive
      (schedule := schedule) hpos)
    hstrict hremaining htail hpayment

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsDerivedSignTailStrictRemainderDenominatorFreeComponentStrictCanonicalRatioShareSum
    {schedule : LiveSingletonOptionShareSchedule}
    (hpaid :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        schedule)
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical
        schedule)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical
        schedule)
    (hpayment :
      ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
        ∀ᶠ n in atTop,
          ∀ H : ℝ, 0 < H →
            ∀ Ω : Finset
              (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
              ∀ v, ∀ _hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
                let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
                let cap := boundaryCrossingCap n Ωnz
                let D :=
                  finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct
                    β H n v
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
                let liveOptions :=
                  finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
                    v Ωnz true true true
                ∀ x ∈ liveOptions,
                  (∑ E ∈
                    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
                      v Ωnz true true true
                      ({x} : Finset (Option (FK.boxVerts 3 n))),
                    finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                      β H E / R) ≤
                    schedule.singletonShare β H Ωnz v x) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsDerivedSignTailStrictRemainderDenominatorFreeRemainderPositive
    (schedule := schedule)
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositive_of_boundaryCrossingCapComponentStrictCanonicalRatioShareSum
      hpaid)
    hstrict hremaining htail hpayment

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsDerivedSignTailStrictRemainderDenominatorFreeNamedPayment
    {schedule : LiveSingletonOptionShareSchedule}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        schedule)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        schedule)
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical
        schedule)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical
        schedule)
    (hpayment :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsPayment
        schedule) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsDerivedSignTailStrictRemainderDenominatorFree
    (schedule := schedule)
    hR hstrict hremaining htail hpayment

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignTailStrictRemainderDenominatorFree
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsDerivedSignTailStrictRemainderDenominatorFreeNamedPayment
    (schedule := liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
    hR
    (liveSingletonOptionShareScheduleStrictTotal_of_residualCaseNormalizedPointwiseRowsCanonicalRaw
      hR hraw)
    (liveSingletonOptionShareScheduleRemaining_of_residualCaseNormalizedPointwiseRowsCanonical
      hR)
    (liveSingletonOptionShareScheduleTail_of_residualCaseNormalizedPointwiseRowsCanonical
      hR)
    liveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsPayment_of_canonical

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignTailStrictRemainderDenominatorFreeRemainderPositive
    (hpos :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignTailStrictRemainderDenominatorFree
    (liveSingletonOptionShareScheduleRemainderPositive_of_boundaryCrossingRemainderPositive
      (schedule := liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
      hpos)
    hraw

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignTailStrictRemainderDenominatorFreeComponentStrictCanonicalRatioShareSum
    (hpaid :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignTailStrictRemainderDenominatorFreeRemainderPositive
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositive_of_boundaryCrossingCapComponentStrictCanonicalRatioShareSum
      hpaid)
    hraw

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsDerivedSignTailStrictRemainderDenominatorFree
    {schedule : LiveSingletonOptionShareSchedule}
    {ι :
      {n : ℕ} →
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
          FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
    [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
    [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
    {label :
      ∀ {n : ℕ},
        (Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) →
          (v : FK.boxVerts 3 n) →
          (x : Option (FK.boxVerts 3 n)) →
            finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
              n v →
              ι Ω v x}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        schedule)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        schedule)
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical
        schedule)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical
        schedule)
    (hpayment :
      ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
        ∀ᶠ n in atTop,
          ∀ H : ℝ, 0 < H →
            ∀ Ω : Finset
              (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
              ∀ v, ∀ _hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
                let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
                let cap := boundaryCrossingCap n Ωnz
                let D :=
                  finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct
                    β H n v
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
                let liveOptions :=
                  finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
                    v Ωnz true true true
                ∀ x ∈ liveOptions,
                  (∑ i : ι Ωnz v x,
                    ∑ E ∈
                      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
                        v Ωnz true true true
                        ({x} : Finset (Option (FK.boxVerts 3 n)))
                        (label Ωnz v x) i,
                      finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                        β H E / R) ≤
                    schedule.singletonShare β H Ωnz v x) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
    boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleDerivedSignTailStrictRemainderDenominatorFree
      hR hstrict hremaining htail
      (liveSingletonOptionShareScheduleSingleton_of_residualCaseNormalizedLabelRows
        (schedule := schedule) (label := label) hR hpayment)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsDerivedSignTailStrictRemainderDenominatorFreeRemainderPositive
    {schedule : LiveSingletonOptionShareSchedule}
    {ι :
      {n : ℕ} →
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
          FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
    [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
    [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
    {label :
      ∀ {n : ℕ},
        (Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) →
          (v : FK.boxVerts 3 n) →
          (x : Option (FK.boxVerts 3 n)) →
            finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
              n v →
              ι Ω v x}
    (hpos :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        schedule)
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical
        schedule)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical
        schedule)
    (hpayment :
      ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
        ∀ᶠ n in atTop,
          ∀ H : ℝ, 0 < H →
            ∀ Ω : Finset
              (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
              ∀ v, ∀ _hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
                let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
                let cap := boundaryCrossingCap n Ωnz
                let D :=
                  finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct
                    β H n v
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
                let liveOptions :=
                  finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
                    v Ωnz true true true
                ∀ x ∈ liveOptions,
                  (∑ i : ι Ωnz v x,
                    ∑ E ∈
                      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
                        v Ωnz true true true
                        ({x} : Finset (Option (FK.boxVerts 3 n)))
                        (label Ωnz v x) i,
                      finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                        β H E / R) ≤
                    schedule.singletonShare β H Ωnz v x) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsDerivedSignTailStrictRemainderDenominatorFree
    (schedule := schedule) (label := label)
    (liveSingletonOptionShareScheduleRemainderPositive_of_boundaryCrossingRemainderPositive
      (schedule := schedule) hpos)
    hstrict hremaining htail hpayment

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsDerivedSignTailStrictRemainderDenominatorFreeComponentStrictCanonicalRatioShareSum
    {schedule : LiveSingletonOptionShareSchedule}
    {ι :
      {n : ℕ} →
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
          FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
    [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
    [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
    {label :
      ∀ {n : ℕ},
        (Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) →
          (v : FK.boxVerts 3 n) →
          (x : Option (FK.boxVerts 3 n)) →
            finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
              n v →
              ι Ω v x}
    (hpaid :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        schedule)
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical
        schedule)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical
        schedule)
    (hpayment :
      ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
        ∀ᶠ n in atTop,
          ∀ H : ℝ, 0 < H →
            ∀ Ω : Finset
              (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
              ∀ v, ∀ _hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
                let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
                let cap := boundaryCrossingCap n Ωnz
                let D :=
                  finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct
                    β H n v
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
                let liveOptions :=
                  finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
                    v Ωnz true true true
                ∀ x ∈ liveOptions,
                  (∑ i : ι Ωnz v x,
                    ∑ E ∈
                      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
                        v Ωnz true true true
                        ({x} : Finset (Option (FK.boxVerts 3 n)))
                        (label Ωnz v x) i,
                      finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                        β H E / R) ≤
                    schedule.singletonShare β H Ωnz v x) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsDerivedSignTailStrictRemainderDenominatorFreeRemainderPositive
    (schedule := schedule) (label := label)
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositive_of_boundaryCrossingCapComponentStrictCanonicalRatioShareSum
      hpaid)
    hstrict hremaining htail hpayment

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsDerivedSignTailStrictRemainderDenominatorFreeNamedPayment
    {schedule : LiveSingletonOptionShareSchedule}
    {ι :
      {n : ℕ} →
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
          FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
    [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
    [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
    {label :
      ∀ {n : ℕ},
        (Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) →
          (v : FK.boxVerts 3 n) →
          (x : Option (FK.boxVerts 3 n)) →
            finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
              n v →
              ι Ω v x}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        schedule)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        schedule)
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical
        schedule)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical
        schedule)
    (hpayment :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsPayment
        label schedule) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsDerivedSignTailStrictRemainderDenominatorFree
    (schedule := schedule) (label := label)
    hR hstrict hremaining htail hpayment

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalDerivedSignTailStrictRemainderDenominatorFree
    {ι :
      {n : ℕ} →
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
          FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
    [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
    [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
    {label :
      ∀ {n : ℕ},
        (Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) →
          (v : FK.boxVerts 3 n) →
          (x : Option (FK.boxVerts 3 n)) →
            finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
              n v →
              ι Ω v x}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        (liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical
          label))
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalPositiveSubcritical
        label) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsDerivedSignTailStrictRemainderDenominatorFreeNamedPayment
    (schedule := liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical
      label)
    (label := label)
    hR
    (liveSingletonOptionShareScheduleStrictTotal_of_residualCaseNormalizedLabelRowsCanonicalRaw
      (label := label) hR hraw)
    (liveSingletonOptionShareScheduleRemaining_of_residualCaseNormalizedLabelRowsCanonical
      (label := label) hR)
    (liveSingletonOptionShareScheduleTail_of_residualCaseNormalizedLabelRowsCanonical
      (label := label) hR)
    (liveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsPayment_of_canonical
      label)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalDerivedSignTailStrictRemainderDenominatorFreeRemainderPositive
    {ι :
      {n : ℕ} →
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
          FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
    [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
    [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
    {label :
      ∀ {n : ℕ},
        (Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) →
          (v : FK.boxVerts 3 n) →
          (x : Option (FK.boxVerts 3 n)) →
            finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
              n v →
              ι Ω v x}
    (hpos :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalPositiveSubcritical
        label) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalDerivedSignTailStrictRemainderDenominatorFree
    (label := label)
    (liveSingletonOptionShareScheduleRemainderPositive_of_boundaryCrossingRemainderPositive
      (schedule := liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical
        label)
      hpos)
    hraw

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalDerivedSignTailStrictRemainderDenominatorFreeComponentStrictCanonicalRatioShareSum
    {ι :
      {n : ℕ} →
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
          FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
    [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
    [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
    {label :
      ∀ {n : ℕ},
        (Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) →
          (v : FK.boxVerts 3 n) →
          (x : Option (FK.boxVerts 3 n)) →
            finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
              n v →
              ι Ω v x}
    (hpaid :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalPositiveSubcritical
        label) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalDerivedSignTailStrictRemainderDenominatorFreeRemainderPositive
    (label := label)
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositive_of_boundaryCrossingCapComponentStrictCanonicalRatioShareSum
      hpaid)
    hraw

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonUniformCapTailStrictRemainderDenominatorFree
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonUniformCapTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonBudgetTailStrictRemainderDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonBudgetTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonUniformCapTailStrictRemainderDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonUniformCapBoxVolumeTailStrictRemainderDenominatorFree
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonUniformCapBoxVolumeTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonUniformCapTailStrictRemainderDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonUniformCapTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonUniformCapBoxVolumeTailStrictRemainderDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonUniformCapFullBoxVolumeTailStrictRemainderDenominatorFree
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonUniformCapFullBoxVolumeTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonUniformCapBoxVolumeTailStrictRemainderDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonUniformCapBoxVolumeTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonUniformCapFullBoxVolumeTailStrictRemainderDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapFullBoxVolumeTailStrictRemainderDenominatorFree
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapFullBoxVolumeTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonUniformCapFullBoxVolumeTailStrictRemainderDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonUniformCapFullBoxVolumeTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapFullBoxVolumeTailStrictRemainderDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapBoxVolumeTailStrictRemainderDenominatorFree
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapBoxVolumeTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonUniformCapBoxVolumeTailStrictRemainderDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonUniformCapBoxVolumeTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapBoxVolumeTailStrictRemainderDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapSupportCountTailStrictRemainderDenominatorFree
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapSupportCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneTailStrictRemainderDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapSupportCountTailStrictRemainderDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapSingletonOptionSupportCountTailStrictRemainderDenominatorFree
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapSingletonOptionSupportCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapSupportCountTailStrictRemainderDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapSupportCountTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapSingletonOptionSupportCountTailStrictRemainderDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantSingletonOptionSupportCountTailStrictRemainderDenominatorFree
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantSingletonOptionSupportCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapSingletonOptionSupportCountTailStrictRemainderDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapSingletonOptionSupportCountTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantSingletonOptionSupportCountTailStrictRemainderDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareSingletonOptionSupportCountTailStrictRemainderDenominatorFree
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareSingletonOptionSupportCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantSingletonOptionSupportCountTailStrictRemainderDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantSingletonOptionSupportCountTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareSingletonOptionSupportCountTailStrictRemainderDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapResidualCaseClassifiedCountTailStrictRemainderDenominatorFree
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapResidualCaseClassifiedCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapSupportCountTailStrictRemainderDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapSupportCountTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapResidualCaseClassifiedCountTailStrictRemainderDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapSingletonOptionClassifiedCountTailStrictRemainderDenominatorFree
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapSingletonOptionClassifiedCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapResidualCaseClassifiedCountTailStrictRemainderDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapResidualCaseClassifiedCountTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapSingletonOptionClassifiedCountTailStrictRemainderDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantSingletonOptionClassifiedCountTailStrictRemainderDenominatorFree
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantSingletonOptionClassifiedCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapSingletonOptionClassifiedCountTailStrictRemainderDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapSingletonOptionClassifiedCountTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantSingletonOptionClassifiedCountTailStrictRemainderDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareSingletonOptionClassifiedCountTailStrictRemainderDenominatorFree
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareSingletonOptionClassifiedCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantSingletonOptionClassifiedCountTailStrictRemainderDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantSingletonOptionClassifiedCountTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareSingletonOptionClassifiedCountTailStrictRemainderDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantResidualCaseClassifiedCountTailStrictRemainderDenominatorFree
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantResidualCaseClassifiedCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapResidualCaseClassifiedCountTailStrictRemainderDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapResidualCaseClassifiedCountTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantResidualCaseClassifiedCountTailStrictRemainderDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareResidualCaseClassifiedCountTailStrictRemainderDenominatorFree
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareResidualCaseClassifiedCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantResidualCaseClassifiedCountTailStrictRemainderDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantResidualCaseClassifiedCountTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareResidualCaseClassifiedCountTailStrictRemainderDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantSupportCountTailStrictRemainderDenominatorFree
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantSupportCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapSupportCountTailStrictRemainderDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapSupportCountTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantSupportCountTailStrictRemainderDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareSupportCountTailStrictRemainderDenominatorFree
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareSupportCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantSupportCountTailStrictRemainderDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantSupportCountTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareSupportCountTailStrictRemainderDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantBoxVolumeTailStrictRemainderDenominatorFree
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantBoxVolumeTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapBoxVolumeTailStrictRemainderDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapBoxVolumeTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantBoxVolumeTailStrictRemainderDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareBoxVolumeTailStrictRemainderDenominatorFree
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareBoxVolumeTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantBoxVolumeTailStrictRemainderDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantBoxVolumeTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareBoxVolumeTailStrictRemainderDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedResidualEnvelopeClassifiedCardExpandedStrictMajorantDenominatorFree
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedResidualEnvelopeClassifiedCardExpandedStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExpandedStrictMajorantDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExpandedStrictMajorantDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedResidualEnvelopeClassifiedCardExpandedStrictMajorantDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedPointwiseClassifiedExpandedStrictMajorantDenominatorFree
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedPointwiseClassifiedExpandedStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExpandedStrictMajorantDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellExpandedStrictMajorantDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedPointwiseClassifiedExpandedStrictMajorantDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedResidualEnvelopeClassifiedCardCanonicalExpandedStrictRemainder
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedResidualEnvelopeClassifiedCardCanonicalExpandedStrictRemainderAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedResidualEnvelopeClassifiedCardExpandedStrictMajorantDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedResidualEnvelopeClassifiedCardExpandedStrictMajorantDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedResidualEnvelopeClassifiedCardCanonicalExpandedStrictRemainder
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedPointwiseClassifiedCanonicalExpandedStrictRemainder
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedPointwiseClassifiedCanonicalExpandedStrictRemainderAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedPointwiseClassifiedExpandedStrictMajorantDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedPointwiseClassifiedExpandedStrictMajorantDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellNamedPointwiseClassifiedCanonicalExpandedStrictRemainder
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFree
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFree
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
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
        ι label) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFree
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
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
        ι label) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderStrictMajorantDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitStrictMajorantDenominatorFree
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
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
        ι label) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellStrictMajorantDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitStrictMajorantDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitResidualEnvelopeClassifiedCardStrictMajorantDenominatorFree
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
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitResidualEnvelopeClassifiedCardStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
        ι label) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitStrictMajorantDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitStrictMajorantDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitResidualEnvelopeClassifiedCardStrictMajorantDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitLabelFreeResidualEnvelopeClassifiedCardStrictMajorantDenominatorFree
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitLabelFreeResidualEnvelopeClassifiedCardStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitResidualEnvelopeClassifiedCardStrictMajorantDenominatorFree
    (ι := fun _ _ _ _ _ _ => Unit)
    (label := fun {_n} _Ω _v _hasGhost _hasOrigin _hasEndpoint _R _E => ())
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitResidualEnvelopeClassifiedCardStrictMajorantDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitLabelFreeResidualEnvelopeClassifiedCardStrictMajorantDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitLabelFreePointwiseClassifiedStrictMajorantDenominatorFree
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitLabelFreePointwiseClassifiedStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitStrictMajorantDenominatorFree
    (ι := fun _ _ _ _ _ _ => Unit)
    (label := fun {_n} _Ω _v _hasGhost _hasOrigin _hasEndpoint _R _E => ())
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitStrictMajorantDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitLabelFreePointwiseClassifiedStrictMajorantDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitRowStrictMajorantDenominatorFree
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
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitRowStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
        ι label) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitStrictMajorantDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitStrictMajorantDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitRowStrictMajorantDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitPointwiseStrictMajorantDenominatorFree
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
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitPointwiseStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
        ι label) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitRowStrictMajorantDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitRowStrictMajorantDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitPointwiseStrictMajorantDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitRowEnvelopeStrictMajorantDenominatorFree
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
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitRowEnvelopeStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
        ι label) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitRowStrictMajorantDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitRowStrictMajorantDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitRowEnvelopeStrictMajorantDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitRowEnvelopeCardMajorantStrictMajorantDenominatorFree
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
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitRowEnvelopeCardMajorantStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
        ι label) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitRowStrictMajorantDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitRowStrictMajorantDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitRowEnvelopeCardMajorantStrictMajorantDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitRowEnvelopeClassifiedCardStrictMajorantDenominatorFree
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
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitRowEnvelopeClassifiedCardStrictMajorantDenominatorFreeAbsorptionPositiveSubcritical
        ι label) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitRowEnvelopeCardMajorantStrictMajorantDenominatorFree
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitRowEnvelopeCardMajorantStrictMajorantDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellExplicitRowEnvelopeClassifiedCardStrictMajorantDenominatorFree
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15BoundaryCrossingRemainderShare
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
    (hcomponent :
      BoundaryCrossingCapComponentSumPositiveSubcritical)
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical
        ι label) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardDependentLabelBudget15BoundaryCrossingRemainderShare
    hcomponent
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardDependentLabelBudget15BoundaryCrossingRemainderShareAbsorption_of_canonicalNormalizedRowDependentLabelBudget15BoundaryCrossingRemainderShare
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShare
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
    (hcomponent :
      BoundaryCrossingCapComponentSumPositiveSubcritical)
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical
        ι label) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15BoundaryCrossingRemainderShare
    hcomponent
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShare
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareRemainderPositive
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
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical
        ι label) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareRemainderPositive
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositive_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShare
      hshare)
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareAbsorption_of_residualThresholdSupportExactCardShellBudget15BoundaryCrossingRemainderShare
      (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardShellBudget15BoundaryCrossingRemainderShareAbsorption_of_dependentLabelBudget15BoundaryCrossingRemainderShare
        (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardDependentLabelBudget15BoundaryCrossingRemainderShareAbsorption_of_canonicalNormalizedRowDependentLabelBudget15BoundaryCrossingRemainderShare
          (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalNormalizedRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShare
            hshare))))

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderMajorantShare
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
    (hcomponent :
      BoundaryCrossingCapComponentSumPositiveSubcritical)
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderMajorantShareAbsorptionPositiveSubcritical
        ι label) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShare
    hcomponent
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderMajorantShare
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderMajorantShareRemainderPositive
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
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderMajorantShareAbsorptionPositiveSubcritical
        ι label) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareRemainderPositive
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderMajorantShare
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellMajorantShare
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
    (hcomponent :
      BoundaryCrossingCapComponentSumPositiveSubcritical)
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellMajorantShareAbsorptionPositiveSubcritical
        ι label) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderMajorantShare
    hcomponent
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderMajorantShareAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellMajorantShare
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellMajorantShareRemainderPositive
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
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellMajorantShareAbsorptionPositiveSubcritical
        ι label) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderMajorantShareRemainderPositive
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderMajorantShareAbsorption_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellMajorantShare
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellMajorantDenominatorFree
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
    (hcomponent :
      BoundaryCrossingCapComponentSumPositiveSubcritical)
    (hpos :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
    (hmajorant :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellMajorantDenominatorFreeAbsorptionPositiveSubcritical
        ι label) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellMajorantShare
    hcomponent
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellMajorantShareAbsorption_of_boundaryCrossingRemainderPositive_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellMajorantDenominatorFree
      hpos hmajorant)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellMajorantDenominatorFreeRemainderPositive
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
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellMajorantShareRemainderPositive
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellMajorantShareAbsorption_of_boundaryCrossingRemainderPositive_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellMajorantDenominatorFree
      hpos hmajorant)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawDenominatorFree
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
    (hcomponent :
      BoundaryCrossingCapComponentSumPositiveSubcritical)
    (hpos :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
    (hraw :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical
        ι label) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellMajorantDenominatorFree
    hcomponent hpos
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellMajorantDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSum
      hraw)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawDenominatorFreeRemainderPositive
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
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellMajorantDenominatorFreeRemainderPositive
    hpos
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderExactShellMajorantDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSum
      hraw)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawDenominatorFreeComponentStrictSum
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
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawDenominatorFreeRemainderPositive
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositive_of_boundaryCrossingCapComponentStrictSum
      hstrict)
    hraw

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawDenominatorFreeComponentStrictShare
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
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawDenominatorFreeComponentStrictSum
    (boundaryCrossingCapComponentStrictSumAbsorption_of_componentStrictShare
      hstrictShare)
    hraw

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawDenominatorFreeComponentStrictCanonicalRatioShareSum
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
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawDenominatorFreeComponentStrictShare
    (boundaryCrossingCapComponentStrictShareAbsorption_of_canonicalRatioShareSum
      hstrict)
    hraw

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawRemainderDenominatorFreeRemainderPositive
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
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareRemainderPositive
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderShareAbsorption_of_boundaryCrossingRemainderPositive_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderDenominatorFree
      hpos hraw)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawRemainderDenominatorFreeComponentStrictCanonicalRatioShareSum
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
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawRemainderDenominatorFreeRemainderPositive
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositive_of_boundaryCrossingCapComponentStrictCanonicalRatioShareSum
      hstrict)
    hraw

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderCanonicalRawRowRatioComponentStrictCanonicalRatioShareSum
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
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawRemainderDenominatorFreeComponentStrictCanonicalRatioShareSum
    hstrict
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderDenominatorFreeAbsorption_of_canonicalRawRowDependentLabelBudget15CanonicalRatioShareSum
      hrawRatio)

set_option linter.style.longLine false in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderResidualThresholdRatioComponentStrictCanonicalRatioShareSum
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
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderCanonicalRawRowRatioComponentStrictCanonicalRatioShareSum
    hstrict
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15CanonicalRatioShareSum_of_residualThresholdShellBudget15CanonicalRatioShareSum
      (ι := ι) (label := label)
      hbudgetRatio)

set_option linter.style.longLine false in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderResidualThresholdStrictCanonicalRatioShareSum
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
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderResidualThresholdRatioComponentStrictCanonicalRatioShareSum
    (ι := ι) (label := label)
    (boundaryCrossingCapComponentStrictCanonicalRatioShareSum_of_residualThresholdShellBudget15StrictCanonicalRatioShareSum
      h)
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15CanonicalRatioShareSum_of_strictCanonicalRatioShareSum
      h)


end Exact3D
end StatMech
