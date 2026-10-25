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
import Abbrev.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part9
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem boundaryCrossingCapBoxRatioComponentSumWithBound_mono
    {capSmall capLarge : BoundaryCrossingCapBound}
    (hle : BoundaryCrossingCapBoundLePositiveSubcritical capSmall capLarge)
    (hlarge :
      BoundaryCrossingCapBoxRatioComponentSumWithBoundPositiveSubcritical
        capLarge) :
    BoundaryCrossingCapBoxRatioComponentSumWithBoundPositiveSubcritical
      capSmall := by
  intro β hβpos hβc
  filter_upwards [hle β hβpos hβc, hlarge β hβpos hβc] with
    n hnle hnlarge
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let oneTerm := boundaryVertexTanhNormalizedOnePointCurrentRatioTerm
    β H n
  let boundaryTerm := boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
    β H n v
  let emptyTerm := boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm
    β H n v
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  have hleCap :
      capSmall β H n Ωnz ≤ capLarge β H n Ωnz := by
    simpa [Ωnz] using hnle H hH Ω
  have honeTerm : 0 ≤ oneTerm := by
    simpa [oneTerm] using
      boundaryVertexTanhNormalizedOnePointCurrentRatioTerm_nonneg hβpos hH
  have hboundaryTerm : 0 ≤ boundaryTerm := by
    simpa [boundaryTerm] using
      boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm_nonneg
        v hβpos hH
  have honeLe :
      capSmall β H n Ωnz * oneTerm ≤
        capLarge β H n Ωnz * oneTerm :=
    mul_le_mul_of_nonneg_right hleCap honeTerm
  have hboundaryLe :
      capSmall β H n Ωnz * boundaryTerm ≤
        capLarge β H n Ωnz * boundaryTerm :=
    mul_le_mul_of_nonneg_right hleCap hboundaryTerm
  have hlargeSum :
      capLarge β H n Ωnz * oneTerm +
          capLarge β H n Ωnz * boundaryTerm +
        emptyTerm ≤ D := by
    simpa [Ωnz, oneTerm, boundaryTerm, emptyTerm, D] using
      hnlarge H hH Ω v hv
  calc
    capSmall β H n Ωnz * oneTerm +
          capSmall β H n Ωnz * boundaryTerm +
        emptyTerm ≤
        capLarge β H n Ωnz * oneTerm +
            capLarge β H n Ωnz * boundaryTerm +
          emptyTerm := by
      linarith
    _ ≤ D := hlargeSum

set_option linter.style.longLine false in


theorem boundaryCrossingCapBoxRatioComponentShareWithBound_mono
    {capSmall capLarge : BoundaryCrossingCapBound}
    (hle : BoundaryCrossingCapBoundLePositiveSubcritical capSmall capLarge)
    (hlarge :
      BoundaryCrossingCapBoxRatioComponentShareWithBoundPositiveSubcritical
        capLarge) :
    BoundaryCrossingCapBoxRatioComponentShareWithBoundPositiveSubcritical
      capSmall := by
  intro β hβpos hβc
  filter_upwards [hle β hβpos hβc, hlarge β hβpos hβc] with
    n hnle hnlarge
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  rcases hnlarge H hH Ω v hv with
    ⟨oneShare, boundaryPairShare, emptyBoundaryShare,
      honeShare, hboundaryShare, hemptyShare, hshareSum,
      honeLarge, hboundaryLarge, hemptyLarge⟩
  have hleCap :
      capSmall β H n Ωnz ≤ capLarge β H n Ωnz := by
    simpa [Ωnz] using hnle H hH Ω
  have honeTerm :
      0 ≤ boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n :=
    boundaryVertexTanhNormalizedOnePointCurrentRatioTerm_nonneg hβpos hH
  have hboundaryTerm :
      0 ≤ boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
        β H n v :=
    boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm_nonneg
      v hβpos hH
  have honeCap :
      capSmall β H n Ωnz *
          boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n ≤
        capLarge β H n Ωnz *
          boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n :=
    mul_le_mul_of_nonneg_right hleCap honeTerm
  have hboundaryCap :
      capSmall β H n Ωnz *
          boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm β H n v ≤
        capLarge β H n Ωnz *
          boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm β H n v :=
    mul_le_mul_of_nonneg_right hleCap hboundaryTerm
  exact
    ⟨oneShare, boundaryPairShare, emptyBoundaryShare,
      honeShare, hboundaryShare, hemptyShare, hshareSum,
      le_trans honeCap honeLarge,
      le_trans hboundaryCap hboundaryLarge,
      hemptyLarge⟩

end Exact3D
end StatMech
