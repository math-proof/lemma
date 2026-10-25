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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part127
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

def BoundaryCrossingCapOnePointThirdWithBoundPositiveSubcritical
    (capBound : BoundaryCrossingCapBound) : Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct
              β H n v
            capBound β H n Ωnz *
                finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                  β H n ≤
              D / 3


def BoundaryCrossingCapBoundaryPairThirdWithBoundPositiveSubcritical
    (capBound : BoundaryCrossingCapBound) : Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct
              β H n v
            capBound β H n Ωnz *
                finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                  β H n v ≤
              D / 3


def BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdWithBoundPositiveSubcritical
    (capBound : BoundaryCrossingCapBound) : Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            capBound β H n Ωnz *
                boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n ≤
              boundaryVertexBoxSimonCurrentRatio β n v / 3


def BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdWithBoundPositiveSubcritical
    (capBound : BoundaryCrossingCapBound) : Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            capBound β H n Ωnz *
                boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
                  β H n v ≤
              boundaryVertexBoxSimonCurrentRatio β n v / 3


def BoundaryCrossingCapEmptyBoundaryThirdPositiveSubcritical : Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ _Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct
              β H n v
            finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                β H n v ≤
              D / 3


def BoundaryCrossingCapTanhNormalizedEmptyBoundaryThirdPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ _Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            boundaryVertexTanhNormalizedEmptyBoundaryTerm β H n v ≤
              boundaryVertexTanhNormalizedSimonDenominator β H n v / 3


def BoundaryCrossingCapTanhNormalizedEmptyBoundaryCurrentRatioThirdPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ _Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm
                β H n v ≤
              boundaryVertexLocalizedSimonCurrentRatio β H n v / 3


def BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ _Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm
                β H n v ≤
              boundaryVertexBoxSimonCurrentRatio β n v / 3

set_option linter.style.longLine false in


def BoundaryCrossingCapBoxRatioEmptyBoundaryCurrentSumThirdPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ _Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let G := Sharpness.withGhost (FK.boxGraph 3 n)
            let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H
              (fun _ => 1)
            let A : Finset (Option (FK.boxVerts 3 n)) :=
              ({some (IsingFK.boxOrigin 3 n)} :
                Finset (Option (FK.boxVerts 3 n))) ∆ {some v}
            ((β * H) / Real.tanh (β * H)) *
                Sharpness.currentSum G β J A ≤
              (boundaryVertexBoxSimonCurrentRatio β n v / 3) *
                Sharpness.currentSum G β J
                  (∅ : Finset (Option (FK.boxVerts 3 n)))

set_option linter.style.longLine false in


def BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedThirdPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ _Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let G := Sharpness.withGhost (FK.boxGraph 3 n)
            let J := boundaryGhostCoupling (FK.boxBoundary 3 n) H
              (fun _ => 1)
            let A : Finset (Option (FK.boxVerts 3 n)) :=
              ({some (IsingFK.boxOrigin 3 n)} :
                Finset (Option (FK.boxVerts 3 n))) ∆ {some v}
            ((β * H) / Real.tanh (β * H)) *
                edgeCopySourcePairEmptyCollapsedSum G β J A ≤
              (boundaryVertexBoxSimonCurrentRatio β n v / 3) *
                edgeCopySourcePairEmptyCollapsedSum G β J
                  (∅ : Finset (Option (FK.boxVerts 3 n)))

end Exact3D
end StatMech
