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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part132
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryScalarUncutoffPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let cardBudget := (Ω.card : ℝ)
            let sourceCardBudget :=
              ∑ m ∈ Ω, ((finiteBoundaryGhostSourceSector m).card : ℝ)
            let edgeBudget :=
              ∑ m ∈ Ω,
                ∑ w ∈ Finset.univ.filter (FK.boxBoundary 3 n),
                  (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ)
            let boundaryCard :=
              ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ)
            (cardBudget *
                  (sourceCardBudget *
                    (boundaryCard * edgeBudget) *
                    (boundaryCard * edgeBudget))) *
                (boundaryVertexTanhNormalizedOnePointCurrentRatioTerm
                    β H n +
                  boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
                    β H n v) +
              boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm
                β H n v ≤
              boundaryVertexBoxSimonCurrentRatio β n v

set_option linter.style.longLine false in


def BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryScalarPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let cardBudget := (Ωnz.card : ℝ)
            let sourceCardBudget :=
              ∑ m ∈ Ωnz, ((finiteBoundaryGhostSourceSector m).card : ℝ)
            let edgeBudget :=
              ∑ m ∈ Ωnz,
                ∑ w ∈ Finset.univ.filter (FK.boxBoundary 3 n),
                  (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ)
            let boundaryCard :=
              ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ)
            (cardBudget *
                  (sourceCardBudget *
                    (boundaryCard * edgeBudget) *
                    (boundaryCard * edgeBudget))) *
                (boundaryVertexTanhNormalizedOnePointCurrentRatioTerm
                    β H n +
                  boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
                    β H n v) +
              boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm
                β H n v ≤
              boundaryVertexBoxSimonCurrentRatio β n v

set_option linter.style.longLine false in


def BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryTwoThirdPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let cardBudget := (Ωnz.card : ℝ)
            let sourceCardBudget :=
              ∑ m ∈ Ωnz, ((finiteBoundaryGhostSourceSector m).card : ℝ)
            let edgeBudget :=
              ∑ m ∈ Ωnz,
                ∑ w ∈ Finset.univ.filter (FK.boxBoundary 3 n),
                  (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ)
            let boundaryCard :=
              ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ)
            (cardBudget *
                  (sourceCardBudget *
                    (boundaryCard * edgeBudget) *
                    (boundaryCard * edgeBudget))) *
                (boundaryVertexTanhNormalizedOnePointCurrentRatioTerm
                    β H n +
                  boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
                    β H n v) ≤
              2 * boundaryVertexBoxSimonCurrentRatio β n v / 3

set_option linter.style.longLine false in

def BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThirdPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let cardBudget := (Ωnz.card : ℝ)
            let sourceCardBudget :=
              ∑ m ∈ Ωnz, ((finiteBoundaryGhostSourceSector m).card : ℝ)
            let edgeBudget :=
              ∑ m ∈ Ωnz,
                ∑ w ∈ Finset.univ.filter (FK.boxBoundary 3 n),
                  (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ)
            let boundaryCard :=
              ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ)
            (cardBudget *
                  (sourceCardBudget *
                    (boundaryCard * edgeBudget) *
                    (boundaryCard * edgeBudget))) *
                boundaryVertexTanhNormalizedOnePointCurrentRatioTerm
                  β H n ≤
              boundaryVertexBoxSimonCurrentRatio β n v / 3

set_option linter.style.longLine false in

def BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThirdPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let cardBudget := (Ωnz.card : ℝ)
            let sourceCardBudget :=
              ∑ m ∈ Ωnz, ((finiteBoundaryGhostSourceSector m).card : ℝ)
            let edgeBudget :=
              ∑ m ∈ Ωnz,
                ∑ w ∈ Finset.univ.filter (FK.boxBoundary 3 n),
                  (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ)
            let boundaryCard :=
              ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ)
            (cardBudget *
                  (sourceCardBudget *
                    (boundaryCard * edgeBudget) *
                    (boundaryCard * edgeBudget))) *
                boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
                  β H n v ≤
              boundaryVertexBoxSimonCurrentRatio β n v / 3

set_option linter.style.longLine false in


def BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointResidualBudgetPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let aggregateBudget :=
              boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
                n Ωnz
            let oneTerm :=
              boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n
            oneTerm = 0 ∨
              aggregateBudget ≤
                (boundaryVertexBoxSimonCurrentRatio β n v / 3) / oneTerm

set_option linter.style.longLine false in


def BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairResidualBudgetPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let aggregateBudget :=
              boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
                n Ωnz
            let boundaryTerm :=
              boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
                β H n v
            boundaryTerm = 0 ∨
              aggregateBudget ≤
                (boundaryVertexBoxSimonCurrentRatio β n v / 3) /
                  boundaryTerm

set_option linter.style.longLine false in


def BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointPositiveRatioResidualBudgetPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let aggregateBudget :=
              boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
                n Ωnz
            let oneTerm :=
              boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n
            0 < oneTerm →
              aggregateBudget ≤
                (boundaryVertexBoxSimonCurrentRatio β n v / 3) / oneTerm

set_option linter.style.longLine false in


def BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairPositiveRatioResidualBudgetPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let aggregateBudget :=
              boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
                n Ωnz
            let boundaryTerm :=
              boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
                β H n v
            0 < boundaryTerm →
              aggregateBudget ≤
                (boundaryVertexBoxSimonCurrentRatio β n v / 3) /
                  boundaryTerm

set_option linter.style.longLine false in


def BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryOnePointResidualBudgetPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let aggregateBudget :=
              boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateExactPolynomialBoundaryBudget
                n Ωnz
            let oneTerm :=
              boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n
            oneTerm = 0 ∨
              aggregateBudget ≤
                (boundaryVertexBoxSimonCurrentRatio β n v / 3) / oneTerm

set_option linter.style.longLine false in


def BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryBoundaryPairResidualBudgetPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let aggregateBudget :=
              boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateExactPolynomialBoundaryBudget
                n Ωnz
            let boundaryTerm :=
              boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
                β H n v
            boundaryTerm = 0 ∨
              aggregateBudget ≤
                (boundaryVertexBoxSimonCurrentRatio β n v / 3) /
                  boundaryTerm

set_option linter.style.longLine false in

def BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryOnePointPositiveRatioResidualBudgetPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let aggregateBudget :=
              boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateExactPolynomialBoundaryBudget
                n Ωnz
            let oneTerm :=
              boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n
            0 < oneTerm →
              aggregateBudget ≤
                (boundaryVertexBoxSimonCurrentRatio β n v / 3) / oneTerm

set_option linter.style.longLine false in

def BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryBoundaryPairPositiveRatioResidualBudgetPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let aggregateBudget :=
              boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateExactPolynomialBoundaryBudget
                n Ωnz
            let boundaryTerm :=
              boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
                β H n v
            0 < boundaryTerm →
              aggregateBudget ≤
                (boundaryVertexBoxSimonCurrentRatio β n v / 3) /
                  boundaryTerm

set_option linter.style.longLine false in


def BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThirdBudgetSchedulePositiveSubcritical
    (onePointBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetSchedule) :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let aggregateBudget :=
              boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
                n Ωnz
            let oneTerm :=
              boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n
            aggregateBudget ≤ onePointBudget β H n Ωnz v ∧
              onePointBudget β H n Ωnz v * oneTerm ≤
                boundaryVertexBoxSimonCurrentRatio β n v / 3

set_option linter.style.longLine false in


def BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThirdBudgetSchedulePositiveSubcritical
    (boundaryPairBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetSchedule) :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let aggregateBudget :=
              boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
                n Ωnz
            let boundaryTerm :=
              boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
                β H n v
            aggregateBudget ≤ boundaryPairBudget β H n Ωnz v ∧
              boundaryPairBudget β H n Ωnz v * boundaryTerm ≤
                boundaryVertexBoxSimonCurrentRatio β n v / 3

set_option linter.style.longLine false in


def BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointBudgetDominationSchedulePositiveSubcritical
    (onePointBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetSchedule) :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let aggregateBudget :=
              boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
                n Ωnz
            aggregateBudget ≤ onePointBudget β H n Ωnz v

set_option linter.style.longLine false in


def BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointBudgetPaymentSchedulePositiveSubcritical
    (onePointBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetSchedule) :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let oneTerm :=
              boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n
            onePointBudget β H n Ωnz v * oneTerm ≤
              boundaryVertexBoxSimonCurrentRatio β n v / 3

set_option linter.style.longLine false in


def BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairBudgetDominationSchedulePositiveSubcritical
    (boundaryPairBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetSchedule) :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let aggregateBudget :=
              boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
                n Ωnz
            aggregateBudget ≤ boundaryPairBudget β H n Ωnz v

set_option linter.style.longLine false in


def BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairBudgetPaymentSchedulePositiveSubcritical
    (boundaryPairBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetSchedule) :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let boundaryTerm :=
              boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
                β H n v
            boundaryPairBudget β H n Ωnz v * boundaryTerm ≤
              boundaryVertexBoxSimonCurrentRatio β n v / 3

set_option linter.style.longLine false in


def BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointBudgetPositiveRatioPaymentSchedulePositiveSubcritical
    (onePointBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetSchedule) :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let oneTerm :=
              boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n
            0 < oneTerm →
              onePointBudget β H n Ωnz v ≤
                (boundaryVertexBoxSimonCurrentRatio β n v / 3) / oneTerm

set_option linter.style.longLine false in


def BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairBudgetPositiveRatioPaymentSchedulePositiveSubcritical
    (boundaryPairBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetSchedule) :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let boundaryTerm :=
              boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
                β H n v
            0 < boundaryTerm →
              boundaryPairBudget β H n Ωnz v ≤
                (boundaryVertexBoxSimonCurrentRatio β n v / 3) /
                  boundaryTerm

set_option linter.style.longLine false in


def BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThirdCardSourceBoundaryEdgeBudgetSchedulePositiveSubcritical
    (cardBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardBudgetSchedule)
    (sourceCardBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioSourceCardBudgetSchedule)
    (edgeMultiplicityBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryGhostEdgeMultiplicityBudgetSchedule) :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let sourceAggregate :=
              ∑ m ∈ Ωnz, ((finiteBoundaryGhostSourceSector m).card : ℝ)
            let edgeAggregate :=
              ∑ m ∈ Ωnz,
                ∑ w ∈ Finset.univ.filter (FK.boxBoundary 3 n),
                  (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ)
            let boundaryCard :=
              ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ)
            (Ωnz.card : ℝ) ≤ cardBudget β H n Ωnz v ∧
              sourceAggregate ≤ sourceCardBudget β H n Ωnz v ∧
              0 ≤ sourceCardBudget β H n Ωnz v ∧
              edgeAggregate ≤ edgeMultiplicityBudget β H n Ωnz v ∧
              0 ≤ edgeMultiplicityBudget β H n Ωnz v ∧
              (cardBudget β H n Ωnz v *
                    (sourceCardBudget β H n Ωnz v *
                      (boundaryCard * edgeMultiplicityBudget β H n Ωnz v) *
                      (boundaryCard * edgeMultiplicityBudget β H n Ωnz v))) *
                  boundaryVertexTanhNormalizedOnePointCurrentRatioTerm
                    β H n ≤
                boundaryVertexBoxSimonCurrentRatio β n v / 3

set_option linter.style.longLine false in


def BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThirdCardSourceBoundaryEdgeBudgetSchedulePositiveSubcritical
    (cardBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardBudgetSchedule)
    (sourceCardBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioSourceCardBudgetSchedule)
    (edgeMultiplicityBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryGhostEdgeMultiplicityBudgetSchedule) :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let sourceAggregate :=
              ∑ m ∈ Ωnz, ((finiteBoundaryGhostSourceSector m).card : ℝ)
            let edgeAggregate :=
              ∑ m ∈ Ωnz,
                ∑ w ∈ Finset.univ.filter (FK.boxBoundary 3 n),
                  (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ)
            let boundaryCard :=
              ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ)
            (Ωnz.card : ℝ) ≤ cardBudget β H n Ωnz v ∧
              sourceAggregate ≤ sourceCardBudget β H n Ωnz v ∧
              0 ≤ sourceCardBudget β H n Ωnz v ∧
              edgeAggregate ≤ edgeMultiplicityBudget β H n Ωnz v ∧
              0 ≤ edgeMultiplicityBudget β H n Ωnz v ∧
              (cardBudget β H n Ωnz v *
                    (sourceCardBudget β H n Ωnz v *
                      (boundaryCard * edgeMultiplicityBudget β H n Ωnz v) *
                      (boundaryCard * edgeMultiplicityBudget β H n Ωnz v))) *
                  boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
                    β H n v ≤
                boundaryVertexBoxSimonCurrentRatio β n v / 3

set_option linter.style.longLine false in


def BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let sourceAggregate :=
              ∑ m ∈ Ωnz, ((finiteBoundaryGhostSourceSector m).card : ℝ)
            let edgeAggregate :=
              ∑ m ∈ Ωnz,
                ∑ w ∈ Finset.univ.filter (FK.boxBoundary 3 n),
                  (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ)
            let boundaryCard :=
              ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ)
            ((Ωnz.card : ℝ) *
                  (sourceAggregate * (boundaryCard * edgeAggregate) *
                    (boundaryCard * edgeAggregate))) *
                boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n ≤
              boundaryVertexBoxSimonCurrentRatio β n v / 3

set_option linter.style.longLine false in


def BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let sourceAggregate :=
              ∑ m ∈ Ωnz, ((finiteBoundaryGhostSourceSector m).card : ℝ)
            let edgeAggregate :=
              ∑ m ∈ Ωnz,
                ∑ w ∈ Finset.univ.filter (FK.boxBoundary 3 n),
                  (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ)
            let boundaryCard :=
              ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ)
            ((Ωnz.card : ℝ) *
                  (sourceAggregate * (boundaryCard * edgeAggregate) *
                    (boundaryCard * edgeAggregate))) *
                boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
                  β H n v ≤
              boundaryVertexBoxSimonCurrentRatio β n v / 3

set_option linter.style.longLine false in


def BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryOnePointActualSchedulePaymentPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let sourceAggregate :=
              ∑ m ∈ Ωnz, ((finiteBoundaryGhostSourceSector m).card : ℝ)
            let edgeAggregate :=
              ∑ m ∈ Ωnz,
                ∑ w ∈ Finset.univ.filter (FK.boxBoundary 3 n),
                  (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ)
            let boundaryCard := 24 * (n : ℝ) ^ 2 + 2
            ((Ωnz.card : ℝ) *
                  (sourceAggregate * (boundaryCard * edgeAggregate) *
                    (boundaryCard * edgeAggregate))) *
                boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n ≤
              boundaryVertexBoxSimonCurrentRatio β n v / 3

set_option linter.style.longLine false in


def BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let sourceAggregate :=
              ∑ m ∈ Ωnz, ((finiteBoundaryGhostSourceSector m).card : ℝ)
            let edgeAggregate :=
              ∑ m ∈ Ωnz,
                ∑ w ∈ Finset.univ.filter (FK.boxBoundary 3 n),
                  (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ)
            let boundaryCard := 24 * (n : ℝ) ^ 2 + 2
            ((Ωnz.card : ℝ) *
                  (sourceAggregate * (boundaryCard * edgeAggregate) *
                    (boundaryCard * edgeAggregate))) *
                boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
                  β H n v ≤
              boundaryVertexBoxSimonCurrentRatio β n v / 3

end Exact3D
end StatMech
