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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part65
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.supportResidualCasePointwiseDependentLabelFieldwiseLeMul_of_normalizedRows
    {β H D : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H) (hDpos : 0 < D)
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {Sh : SourceClassEndpointMembershipResidualShellShare15 v}
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
    (hzeroNone :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).zero_none ≤ Sh.zero_none * D)
    (htwoNone :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_none ≤ Sh.two_none * D)
    (htwoEndpoint :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_endpoint ≤ Sh.two_endpoint * D)
    (htwoOrigin :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_origin ≤ Sh.two_origin * D)
    (htwoGhost :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_ghost ≤ Sh.two_ghost * D)
    (htwoGhostEndpoint :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_ghost_endpoint ≤
          Sh.two_ghost_endpoint * D)
    (htwoGhostOrigin :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_ghost_origin ≤ Sh.two_ghost_origin * D)
    (hfour :
      ∀ hasGhost hasOrigin hasEndpoint k,
        k ∈
            finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
              v hasGhost hasOrigin hasEndpoint →
          Sh.fourShare hasGhost hasOrigin hasEndpoint k =
            ∑ R ∈
              finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                v k,
              ∑ i : ι hasGhost hasOrigin hasEndpoint R,
                ∑ E ∈
                  finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
                    v Ω hasGhost hasOrigin hasEndpoint R
                    (label hasGhost hasOrigin hasEndpoint R) i,
                  finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                    β H E / D) :
    Sh.SupportResidualCasePointwiseDependentLabelFieldwiseLeMul
      β H Ω D ι label := by
  refine
    ⟨hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact
      SourceClassEndpointMembershipResidualShellShare15.supportResidualCasePointwiseDependentLabelField_of_normalizedRows
        (v := v) (β := β) (H := H) (D := D) (Ω := Ω)
        (hasGhost := false) (hasOrigin := false) (hasEndpoint := false)
        (fieldShare := Sh.four_none)
        (ι := ι false false false) (label := label false false false)
        hβ hH hDpos
        (fun k hk => by
          simpa [SourceClassEndpointMembershipResidualShellShare15.fourShare]
            using hfour false false false k hk)
  · exact
      SourceClassEndpointMembershipResidualShellShare15.supportResidualCasePointwiseDependentLabelField_of_normalizedRows
        (v := v) (β := β) (H := H) (D := D) (Ω := Ω)
        (hasGhost := false) (hasOrigin := false) (hasEndpoint := true)
        (fieldShare := Sh.four_endpoint)
        (ι := ι false false true) (label := label false false true)
        hβ hH hDpos
        (fun k hk => by
          simpa [SourceClassEndpointMembershipResidualShellShare15.fourShare]
            using hfour false false true k hk)
  · exact
      SourceClassEndpointMembershipResidualShellShare15.supportResidualCasePointwiseDependentLabelField_of_normalizedRows
        (v := v) (β := β) (H := H) (D := D) (Ω := Ω)
        (hasGhost := false) (hasOrigin := true) (hasEndpoint := false)
        (fieldShare := Sh.four_origin)
        (ι := ι false true false) (label := label false true false)
        hβ hH hDpos
        (fun k hk => by
          simpa [SourceClassEndpointMembershipResidualShellShare15.fourShare]
            using hfour false true false k hk)
  · exact
      SourceClassEndpointMembershipResidualShellShare15.supportResidualCasePointwiseDependentLabelField_of_normalizedRows
        (v := v) (β := β) (H := H) (D := D) (Ω := Ω)
        (hasGhost := false) (hasOrigin := true) (hasEndpoint := true)
        (fieldShare := Sh.four_origin_endpoint)
        (ι := ι false true true) (label := label false true true)
        hβ hH hDpos
        (fun k hk => by
          simpa [SourceClassEndpointMembershipResidualShellShare15.fourShare]
            using hfour false true true k hk)
  · exact
      SourceClassEndpointMembershipResidualShellShare15.supportResidualCasePointwiseDependentLabelField_of_normalizedRows
        (v := v) (β := β) (H := H) (D := D) (Ω := Ω)
        (hasGhost := true) (hasOrigin := false) (hasEndpoint := false)
        (fieldShare := Sh.four_ghost)
        (ι := ι true false false) (label := label true false false)
        hβ hH hDpos
        (fun k hk => by
          simpa [SourceClassEndpointMembershipResidualShellShare15.fourShare]
            using hfour true false false k hk)
  · exact
      SourceClassEndpointMembershipResidualShellShare15.supportResidualCasePointwiseDependentLabelField_of_normalizedRows
        (v := v) (β := β) (H := H) (D := D) (Ω := Ω)
        (hasGhost := true) (hasOrigin := false) (hasEndpoint := true)
        (fieldShare := Sh.four_ghost_endpoint)
        (ι := ι true false true) (label := label true false true)
        hβ hH hDpos
        (fun k hk => by
          simpa [SourceClassEndpointMembershipResidualShellShare15.fourShare]
            using hfour true false true k hk)
  · exact
      SourceClassEndpointMembershipResidualShellShare15.supportResidualCasePointwiseDependentLabelField_of_normalizedRows
        (v := v) (β := β) (H := H) (D := D) (Ω := Ω)
        (hasGhost := true) (hasOrigin := true) (hasEndpoint := false)
        (fieldShare := Sh.four_ghost_origin)
        (ι := ι true true false) (label := label true true false)
        hβ hH hDpos
        (fun k hk => by
          simpa [SourceClassEndpointMembershipResidualShellShare15.fourShare]
            using hfour true true false k hk)
  · exact
      SourceClassEndpointMembershipResidualShellShare15.supportResidualCasePointwiseDependentLabelField_of_normalizedRows
        (v := v) (β := β) (H := H) (D := D) (Ω := Ω)
        (hasGhost := true) (hasOrigin := true) (hasEndpoint := true)
        (fieldShare := Sh.four_ghost_origin_endpoint)
        (ι := ι true true true) (label := label true true true)
        hβ hH hDpos
        (fun k hk => by
          simpa [SourceClassEndpointMembershipResidualShellShare15.fourShare]
            using hfour true true true k hk)

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.supportResidualCaseDependentLabelFieldwiseLeMul_of_pointwiseDependentLabelFieldwiseLeMul
    {β H D : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {Sh : SourceClassEndpointMembershipResidualShellShare15 v}
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
    (h :
      Sh.SupportResidualCasePointwiseDependentLabelFieldwiseLeMul
        β H Ω D ι label) :
    Sh.SupportResidualCaseDependentLabelFieldwiseLeMul β H Ω D ι label := by
  rcases h with
    ⟨hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, hfourNone, hfourEndpoint,
      hfourOrigin, hfourOriginEndpoint, hfourGhost, hfourGhostEndpoint,
      hfourGhostOrigin, hfourGhostOriginEndpoint⟩
  exact
    ⟨hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin,
      SourceClassEndpointMembershipResidualShellShare15.supportResidualCaseDependentLabelField_of_pointwiseDependentLabelField
        (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
        (hasGhost := false) (hasOrigin := false) (hasEndpoint := false)
        (fieldShare := Sh.four_none)
        (ι := ι false false false) (label := label false false false)
        hfourNone,
      SourceClassEndpointMembershipResidualShellShare15.supportResidualCaseDependentLabelField_of_pointwiseDependentLabelField
        (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
        (hasGhost := false) (hasOrigin := false) (hasEndpoint := true)
        (fieldShare := Sh.four_endpoint)
        (ι := ι false false true) (label := label false false true)
        hfourEndpoint,
      SourceClassEndpointMembershipResidualShellShare15.supportResidualCaseDependentLabelField_of_pointwiseDependentLabelField
        (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
        (hasGhost := false) (hasOrigin := true) (hasEndpoint := false)
        (fieldShare := Sh.four_origin)
        (ι := ι false true false) (label := label false true false)
        hfourOrigin,
      SourceClassEndpointMembershipResidualShellShare15.supportResidualCaseDependentLabelField_of_pointwiseDependentLabelField
        (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
        (hasGhost := false) (hasOrigin := true) (hasEndpoint := true)
        (fieldShare := Sh.four_origin_endpoint)
        (ι := ι false true true) (label := label false true true)
        hfourOriginEndpoint,
      SourceClassEndpointMembershipResidualShellShare15.supportResidualCaseDependentLabelField_of_pointwiseDependentLabelField
        (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
        (hasGhost := true) (hasOrigin := false) (hasEndpoint := false)
        (fieldShare := Sh.four_ghost)
        (ι := ι true false false) (label := label true false false)
        hfourGhost,
      SourceClassEndpointMembershipResidualShellShare15.supportResidualCaseDependentLabelField_of_pointwiseDependentLabelField
        (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
        (hasGhost := true) (hasOrigin := false) (hasEndpoint := true)
        (fieldShare := Sh.four_ghost_endpoint)
        (ι := ι true false true) (label := label true false true)
        hfourGhostEndpoint,
      SourceClassEndpointMembershipResidualShellShare15.supportResidualCaseDependentLabelField_of_pointwiseDependentLabelField
        (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
        (hasGhost := true) (hasOrigin := true) (hasEndpoint := false)
        (fieldShare := Sh.four_ghost_origin)
        (ι := ι true true false) (label := label true true false)
        hfourGhostOrigin,
      SourceClassEndpointMembershipResidualShellShare15.supportResidualCaseDependentLabelField_of_pointwiseDependentLabelField
        (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
        (hasGhost := true) (hasOrigin := true) (hasEndpoint := true)
        (fieldShare := Sh.four_ghost_origin_endpoint)
        (ι := ι true true true) (label := label true true true)
        hfourGhostOriginEndpoint⟩

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.supportResidualCaseField_of_dependentLabelField
    {β H D : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool}
    {fieldShare : ℕ → ℝ}
    {ι : Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ R, Fintype (ι R)] [∀ R, DecidableEq (ι R)]
    {label :
      ∀ R,
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ι R}
    (h :
      SourceClassEndpointMembershipResidualShellShare15.SupportResidualCaseDependentLabelField
        β H Ω D hasGhost hasOrigin hasEndpoint fieldShare ι label) :
    ∀ k, k ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v hasGhost hasOrigin hasEndpoint →
      ∃ residualShare : Finset (Option (FK.boxVerts 3 n)) → ℝ,
        fieldShare k =
            ∑ R ∈
              finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                v k,
              residualShare R ∧
          ∀ R, R ∈
              finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                v k →
            SourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare
              v β H Ω hasGhost hasOrigin hasEndpoint R
              (residualShare R) D := by
  intro k hk
  rcases h k hk with ⟨labelShare, hshare, hcases⟩
  refine ⟨fun R => ∑ i : ι R, labelShare R i, hshare, ?_⟩
  intro R hR
  exact
    sourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare_of_labelShares
      (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
      (hasGhost := hasGhost) (hasOrigin := hasOrigin)
      (hasEndpoint := hasEndpoint) (R := R)
      (ι := ι R) (label := label R) (labelShare := labelShare R)
      (hcases R hR)

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.supportResidualCaseFieldwiseLeMul_of_dependentLabelFields
    {β H D : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {Sh : SourceClassEndpointMembershipResidualShellShare15 v}
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
    (hzeroNone :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).zero_none ≤ Sh.zero_none * D)
    (htwoNone :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_none ≤ Sh.two_none * D)
    (htwoEndpoint :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_endpoint ≤ Sh.two_endpoint * D)
    (htwoOrigin :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_origin ≤ Sh.two_origin * D)
    (htwoGhost :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_ghost ≤ Sh.two_ghost * D)
    (htwoGhostEndpoint :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_ghost_endpoint ≤
          Sh.two_ghost_endpoint * D)
    (htwoGhostOrigin :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_ghost_origin ≤ Sh.two_ghost_origin * D)
    (hfourNone :
      SourceClassEndpointMembershipResidualShellShare15.SupportResidualCaseDependentLabelField
        β H Ω D false false false Sh.four_none (ι false false false)
        (label false false false))
    (hfourEndpoint :
      SourceClassEndpointMembershipResidualShellShare15.SupportResidualCaseDependentLabelField
        β H Ω D false false true Sh.four_endpoint
        (ι false false true) (label false false true))
    (hfourOrigin :
      SourceClassEndpointMembershipResidualShellShare15.SupportResidualCaseDependentLabelField
        β H Ω D false true false Sh.four_origin
        (ι false true false) (label false true false))
    (hfourOriginEndpoint :
      SourceClassEndpointMembershipResidualShellShare15.SupportResidualCaseDependentLabelField
        β H Ω D false true true Sh.four_origin_endpoint
        (ι false true true) (label false true true))
    (hfourGhost :
      SourceClassEndpointMembershipResidualShellShare15.SupportResidualCaseDependentLabelField
        β H Ω D true false false Sh.four_ghost
        (ι true false false) (label true false false))
    (hfourGhostEndpoint :
      SourceClassEndpointMembershipResidualShellShare15.SupportResidualCaseDependentLabelField
        β H Ω D true false true Sh.four_ghost_endpoint
        (ι true false true) (label true false true))
    (hfourGhostOrigin :
      SourceClassEndpointMembershipResidualShellShare15.SupportResidualCaseDependentLabelField
        β H Ω D true true false Sh.four_ghost_origin
        (ι true true false) (label true true false))
    (hfourGhostOriginEndpoint :
      SourceClassEndpointMembershipResidualShellShare15.SupportResidualCaseDependentLabelField
        β H Ω D true true true Sh.four_ghost_origin_endpoint
        (ι true true true) (label true true true)) :
    Sh.SupportResidualCaseFieldwiseLeMul β H Ω D := by
  refine
    ⟨hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact
      SourceClassEndpointMembershipResidualShellShare15.supportResidualCaseField_of_dependentLabelField
        (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
        (hasGhost := false) (hasOrigin := false) (hasEndpoint := false)
        (fieldShare := Sh.four_none)
        (ι := ι false false false) (label := label false false false)
        hfourNone
  · exact
      SourceClassEndpointMembershipResidualShellShare15.supportResidualCaseField_of_dependentLabelField
        (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
        (hasGhost := false) (hasOrigin := false) (hasEndpoint := true)
        (fieldShare := Sh.four_endpoint)
        (ι := ι false false true) (label := label false false true)
        hfourEndpoint
  · exact
      SourceClassEndpointMembershipResidualShellShare15.supportResidualCaseField_of_dependentLabelField
        (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
        (hasGhost := false) (hasOrigin := true) (hasEndpoint := false)
        (fieldShare := Sh.four_origin)
        (ι := ι false true false) (label := label false true false)
        hfourOrigin
  · exact
      SourceClassEndpointMembershipResidualShellShare15.supportResidualCaseField_of_dependentLabelField
        (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
        (hasGhost := false) (hasOrigin := true) (hasEndpoint := true)
        (fieldShare := Sh.four_origin_endpoint)
        (ι := ι false true true) (label := label false true true)
        hfourOriginEndpoint
  · exact
      SourceClassEndpointMembershipResidualShellShare15.supportResidualCaseField_of_dependentLabelField
        (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
        (hasGhost := true) (hasOrigin := false) (hasEndpoint := false)
        (fieldShare := Sh.four_ghost)
        (ι := ι true false false) (label := label true false false)
        hfourGhost
  · exact
      SourceClassEndpointMembershipResidualShellShare15.supportResidualCaseField_of_dependentLabelField
        (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
        (hasGhost := true) (hasOrigin := false) (hasEndpoint := true)
        (fieldShare := Sh.four_ghost_endpoint)
        (ι := ι true false true) (label := label true false true)
        hfourGhostEndpoint
  · exact
      SourceClassEndpointMembershipResidualShellShare15.supportResidualCaseField_of_dependentLabelField
        (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
        (hasGhost := true) (hasOrigin := true) (hasEndpoint := false)
        (fieldShare := Sh.four_ghost_origin)
        (ι := ι true true false) (label := label true true false)
        hfourGhostOrigin
  · exact
      SourceClassEndpointMembershipResidualShellShare15.supportResidualCaseField_of_dependentLabelField
        (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
        (hasGhost := true) (hasOrigin := true) (hasEndpoint := true)
        (fieldShare := Sh.four_ghost_origin_endpoint)
        (ι := ι true true true) (label := label true true true)
        hfourGhostOriginEndpoint

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.supportResidualCaseFieldwiseLeMul_of_dependentLabelFieldwiseLeMul
    {β H D : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {Sh : SourceClassEndpointMembershipResidualShellShare15 v}
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
    (h :
      Sh.SupportResidualCaseDependentLabelFieldwiseLeMul
        β H Ω D ι label) :
    Sh.SupportResidualCaseFieldwiseLeMul β H Ω D := by
  rcases h with
    ⟨hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, hfourNone, hfourEndpoint,
      hfourOrigin, hfourOriginEndpoint, hfourGhost, hfourGhostEndpoint,
      hfourGhostOrigin, hfourGhostOriginEndpoint⟩
  exact
    SourceClassEndpointMembershipResidualShellShare15.supportResidualCaseFieldwiseLeMul_of_dependentLabelFields
      (Sh := Sh) (β := β) (H := H) (Ω := Ω) (D := D)
      (ι := ι) (label := label)
      hzeroNone htwoNone htwoEndpoint htwoOrigin htwoGhost
      htwoGhostEndpoint htwoGhostOrigin hfourNone hfourEndpoint
      hfourOrigin hfourOriginEndpoint hfourGhost hfourGhostEndpoint
      hfourGhostOrigin hfourGhostOriginEndpoint

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.supportFieldwiseLeMul_of_residualCaseFieldwiseLeMul
    {β H D : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    {Sh : SourceClassEndpointMembershipResidualShellShare15 v}
    (h : Sh.SupportResidualCaseFieldwiseLeMul β H Ω D) :
    Sh.SupportFieldwiseLeMul β H Ω D := by
  rcases h with
    ⟨hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, hfourNone, hfourEndpoint,
      hfourOrigin, hfourOriginEndpoint, hfourGhost, hfourGhostEndpoint,
      hfourGhostOrigin, hfourGhostOriginEndpoint⟩
  refine
    SourceClassEndpointMembershipResidualShellShare15.supportFieldwiseLeMul_of_cellShares
      hzeroNone htwoNone htwoEndpoint htwoOrigin htwoGhost
      htwoGhostEndpoint htwoGhostOrigin ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro k hk
    rcases hfourNone k hk with ⟨residualShare, hshare, hcases⟩
    simpa [hshare] using
      sourceClassEndpointMembershipSupportResidualExactCardShellCellShare_of_residualCaseShares
        (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
        hv hk (residualShare := residualShare) hcases
  · intro k hk
    rcases hfourEndpoint k hk with ⟨residualShare, hshare, hcases⟩
    simpa [hshare] using
      sourceClassEndpointMembershipSupportResidualExactCardShellCellShare_of_residualCaseShares
        (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
        hv hk (residualShare := residualShare) hcases
  · intro k hk
    rcases hfourOrigin k hk with ⟨residualShare, hshare, hcases⟩
    simpa [hshare] using
      sourceClassEndpointMembershipSupportResidualExactCardShellCellShare_of_residualCaseShares
        (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
        hv hk (residualShare := residualShare) hcases
  · intro k hk
    rcases hfourOriginEndpoint k hk with
      ⟨residualShare, hshare, hcases⟩
    simpa [hshare] using
      sourceClassEndpointMembershipSupportResidualExactCardShellCellShare_of_residualCaseShares
        (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
        hv hk (residualShare := residualShare) hcases
  · intro k hk
    rcases hfourGhost k hk with ⟨residualShare, hshare, hcases⟩
    simpa [hshare] using
      sourceClassEndpointMembershipSupportResidualExactCardShellCellShare_of_residualCaseShares
        (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
        hv hk (residualShare := residualShare) hcases
  · intro k hk
    rcases hfourGhostEndpoint k hk with
      ⟨residualShare, hshare, hcases⟩
    simpa [hshare] using
      sourceClassEndpointMembershipSupportResidualExactCardShellCellShare_of_residualCaseShares
        (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
        hv hk (residualShare := residualShare) hcases
  · intro k hk
    rcases hfourGhostOrigin k hk with
      ⟨residualShare, hshare, hcases⟩
    simpa [hshare] using
      sourceClassEndpointMembershipSupportResidualExactCardShellCellShare_of_residualCaseShares
        (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
        hv hk (residualShare := residualShare) hcases
  · intro k hk
    rcases hfourGhostOriginEndpoint k hk with
      ⟨residualShare, hshare, hcases⟩
    simpa [hshare] using
      sourceClassEndpointMembershipSupportResidualExactCardShellCellShare_of_residualCaseShares
        (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
        hv hk (residualShare := residualShare) hcases

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.supportFieldwiseLeMul_of_dependentLabelFieldwiseLeMul
    {β H D : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    {Sh : SourceClassEndpointMembershipResidualShellShare15 v}
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
    (h :
      Sh.SupportResidualCaseDependentLabelFieldwiseLeMul
        β H Ω D ι label) :
    Sh.SupportFieldwiseLeMul β H Ω D :=
  SourceClassEndpointMembershipResidualShellShare15.supportFieldwiseLeMul_of_residualCaseFieldwiseLeMul
    hv
    (SourceClassEndpointMembershipResidualShellShare15.supportResidualCaseFieldwiseLeMul_of_dependentLabelFieldwiseLeMul
      (Sh := Sh) (β := β) (H := H) (Ω := Ω) (D := D)
      (ι := ι) (label := label) h)

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.fieldwiseLeMul_of_supportFieldwiseLeMul
    {β H D : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    {Sh : SourceClassEndpointMembershipResidualShellShare15 v}
    (h : Sh.SupportFieldwiseLeMul β H Ω D) :
    Sh.FieldwiseLeMul β H Ω D := by
  rcases h with
    ⟨hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, hfourNone, hfourEndpoint,
      hfourOrigin, hfourOriginEndpoint, hfourGhost, hfourGhostEndpoint,
      hfourGhostOrigin, hfourGhostOriginEndpoint⟩
  refine
    ⟨hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    simpa [
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum,
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum_eq_sourceClassSupport_endpointMembership_fourPlus_unmarkedResidualCard_sum_of_boundary_of_mem_shellIndex
        β H n Ω v hv false false false hk] using
      hfourNone k hk
  · intro k hk
    simpa [
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum,
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum_eq_sourceClassSupport_endpointMembership_fourPlus_unmarkedResidualCard_sum_of_boundary_of_mem_shellIndex
        β H n Ω v hv false false true hk] using
      hfourEndpoint k hk
  · intro k hk
    simpa [
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum,
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum_eq_sourceClassSupport_endpointMembership_fourPlus_unmarkedResidualCard_sum_of_boundary_of_mem_shellIndex
        β H n Ω v hv false true false hk] using
      hfourOrigin k hk
  · intro k hk
    simpa [
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum,
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum_eq_sourceClassSupport_endpointMembership_fourPlus_unmarkedResidualCard_sum_of_boundary_of_mem_shellIndex
        β H n Ω v hv false true true hk] using
      hfourOriginEndpoint k hk
  · intro k hk
    simpa [
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum,
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum_eq_sourceClassSupport_endpointMembership_fourPlus_unmarkedResidualCard_sum_of_boundary_of_mem_shellIndex
        β H n Ω v hv true false false hk] using
      hfourGhost k hk
  · intro k hk
    simpa [
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum,
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum_eq_sourceClassSupport_endpointMembership_fourPlus_unmarkedResidualCard_sum_of_boundary_of_mem_shellIndex
        β H n Ω v hv true false true hk] using
      hfourGhostEndpoint k hk
  · intro k hk
    simpa [
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum,
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum_eq_sourceClassSupport_endpointMembership_fourPlus_unmarkedResidualCard_sum_of_boundary_of_mem_shellIndex
        β H n Ω v hv true true false hk] using
      hfourGhostOrigin k hk
  · intro k hk
    simpa [
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum,
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum_eq_sourceClassSupport_endpointMembership_fourPlus_unmarkedResidualCard_sum_of_boundary_of_mem_shellIndex
        β H n Ω v hv true true true hk] using
      hfourGhostOriginEndpoint k hk

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.fieldwiseLeMul_of_dependentLabelFieldwiseLeMul
    {β H D : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    {Sh : SourceClassEndpointMembershipResidualShellShare15 v}
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
    (h :
      Sh.SupportResidualCaseDependentLabelFieldwiseLeMul
        β H Ω D ι label) :
    Sh.FieldwiseLeMul β H Ω D :=
  SourceClassEndpointMembershipResidualShellShare15.fieldwiseLeMul_of_supportFieldwiseLeMul
    hv
    (SourceClassEndpointMembershipResidualShellShare15.supportFieldwiseLeMul_of_dependentLabelFieldwiseLeMul
      (Sh := Sh) (β := β) (H := H) (Ω := Ω) (D := D)
      (ι := ι) (label := label) hv h)

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.toBudget15_fieldwiseLeMul
    {β H D : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {Sh : SourceClassEndpointMembershipResidualShellShare15 v}
    (h : Sh.FieldwiseLeMul β H Ω D) :
    SourceClassEndpointMembershipLiveBudget15.FieldwiseLeMul
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v) Sh.toBudget15 D := by
  rcases h with
    ⟨hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, hfourNone, hfourEndpoint,
      hfourOrigin, hfourOriginEndpoint, hfourGhost, hfourGhostEndpoint,
      hfourGhostOrigin, hfourGhostOriginEndpoint⟩
  refine
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [SourceClassEndpointMembershipResidualShellShare15.toBudget15]
      using hzeroNone
  · simpa [SourceClassEndpointMembershipResidualShellShare15.toBudget15]
      using htwoNone
  · simpa [SourceClassEndpointMembershipResidualShellShare15.toBudget15]
      using htwoEndpoint
  · simpa [SourceClassEndpointMembershipResidualShellShare15.toBudget15]
      using htwoOrigin
  · simpa [SourceClassEndpointMembershipResidualShellShare15.toBudget15]
      using htwoGhost
  · simpa [SourceClassEndpointMembershipResidualShellShare15.toBudget15]
      using htwoGhostEndpoint
  · simpa [SourceClassEndpointMembershipResidualShellShare15.toBudget15]
      using htwoGhostOrigin
  · simpa [
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15]
      using
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_le_shellShareMul
          (share := Sh.four_none) (D := D) hfourNone
  · simpa [
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15]
      using
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_le_shellShareMul
          (share := Sh.four_endpoint) (D := D) hfourEndpoint
  · simpa [
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15]
      using
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_le_shellShareMul
          (share := Sh.four_origin) (D := D) hfourOrigin
  · simpa [
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15]
      using
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_le_shellShareMul
          (share := Sh.four_origin_endpoint) (D := D) hfourOriginEndpoint
  · simpa [
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15]
      using
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_le_shellShareMul
          (share := Sh.four_ghost) (D := D) hfourGhost
  · simpa [
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15]
      using
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_le_shellShareMul
          (share := Sh.four_ghost_endpoint) (D := D) hfourGhostEndpoint
  · simpa [
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15]
      using
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_le_shellShareMul
          (share := Sh.four_ghost_origin) (D := D) hfourGhostOrigin
  · simpa [
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15]
      using
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_le_shellShareMul
          (share := Sh.four_ghost_origin_endpoint) (D := D)
          hfourGhostOriginEndpoint

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipResidualBudget15_total_eq_threshold_total
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualBudget15
        β H n Ω v).total =
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdBudget15
        β H n Ω v).total := by
  simp [
    finiteBoundaryGhostSourceClassEndpointMembershipResidualBudget15,
    finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdBudget15,
    finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15,
    SourceClassEndpointMembershipLiveBudget15.total,
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualCardImageSourceClassSum_eq_thresholdImageSourceClassSum
      β H n Ω v hv]

end Exact3D
end StatMech
