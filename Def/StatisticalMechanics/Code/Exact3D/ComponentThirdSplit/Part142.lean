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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part129
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

def BoundaryCrossingCapBoxRatioComponentSharePositiveSubcritical : Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let cap := boundaryCrossingCap n Ωnz
            ∃ oneShare boundaryPairShare emptyBoundaryShare : ℝ,
              0 ≤ oneShare ∧
              0 ≤ boundaryPairShare ∧
              0 ≤ emptyBoundaryShare ∧
              oneShare + boundaryPairShare + emptyBoundaryShare ≤ 1 ∧
              cap *
                  boundaryVertexTanhNormalizedOnePointCurrentRatioTerm
                    β H n ≤
                oneShare * boundaryVertexBoxSimonCurrentRatio β n v ∧
              cap *
                  boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
                    β H n v ≤
                boundaryPairShare * boundaryVertexBoxSimonCurrentRatio β n v ∧
              boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm
                β H n v ≤
              emptyBoundaryShare * boundaryVertexBoxSimonCurrentRatio β n v


def BoundaryCrossingCapBoxRatioComponentShareWithBoundPositiveSubcritical
    (capBound : BoundaryCrossingCapBound) : Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            ∃ oneShare boundaryPairShare emptyBoundaryShare : ℝ,
              0 ≤ oneShare ∧
              0 ≤ boundaryPairShare ∧
              0 ≤ emptyBoundaryShare ∧
              oneShare + boundaryPairShare + emptyBoundaryShare ≤ 1 ∧
              capBound β H n Ωnz *
                  boundaryVertexTanhNormalizedOnePointCurrentRatioTerm
                    β H n ≤
                oneShare * boundaryVertexBoxSimonCurrentRatio β n v ∧
              capBound β H n Ωnz *
                  boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
                    β H n v ≤
                boundaryPairShare * boundaryVertexBoxSimonCurrentRatio β n v ∧
              boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm
                β H n v ≤
              emptyBoundaryShare * boundaryVertexBoxSimonCurrentRatio β n v

set_option linter.style.longLine false in


def BoundaryCrossingCapBoxRatioComponentSumWithBoundPositiveSubcritical
    (capBound : BoundaryCrossingCapBound) : Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            capBound β H n Ωnz *
                boundaryVertexTanhNormalizedOnePointCurrentRatioTerm
                  β H n +
              capBound β H n Ωnz *
                boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
                  β H n v +
              boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm
                β H n v ≤
              boundaryVertexBoxSimonCurrentRatio β n v

end Exact3D
end StatMech
