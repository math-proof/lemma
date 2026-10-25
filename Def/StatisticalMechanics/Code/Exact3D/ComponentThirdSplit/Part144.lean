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
import Abbrev.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part11
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in

noncomputable def boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioActualCardBudgetSchedule :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardBudgetSchedule :=
  fun _β _H _n Ω _v => (Ω.card : ℝ)

set_option linter.style.longLine false in


noncomputable def boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioSourceCardAggregateBudgetSchedule :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioSourceCardBudgetSchedule :=
  fun _β _H _n Ω _v =>
    ∑ m ∈ Ω, ((finiteBoundaryGhostSourceSector m).card : ℝ)

set_option linter.style.longLine false in


noncomputable def boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryGhostEdgeAggregateBudgetSchedule :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryGhostEdgeMultiplicityBudgetSchedule :=
  fun _β _H n Ω _v =>
    ∑ m ∈ Ω,
      ∑ w ∈ Finset.univ.filter (FK.boxBoundary 3 n),
        (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ)

set_option linter.style.longLine false in


def BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoffPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            ∃ capBudget : ℝ,
              boundaryCrossingCapSourceSectorMultiplicitySquareBound
                  β H n Ω ≤ capBudget ∧
              capBudget *
                    (boundaryVertexTanhNormalizedOnePointCurrentRatioTerm
                        β H n +
                      boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
                        β H n v) +
                  boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm
                    β H n v ≤
                boundaryVertexBoxSimonCurrentRatio β n v

set_option linter.style.longLine false in


def BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoffPositiveSubcritical
    (capBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetSchedule) :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            boundaryCrossingCapSourceSectorMultiplicitySquareBound β H n Ω ≤
                capBudget β H n Ω v ∧
              capBudget β H n Ω v *
                    (boundaryVertexTanhNormalizedOnePointCurrentRatioTerm
                        β H n +
                      boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
                        β H n v) +
                  boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm
                    β H n v ≤
                boundaryVertexBoxSimonCurrentRatio β n v

set_option linter.style.longLine false in


def BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardSummandBudgetScheduleUncutoffPositiveSubcritical
    (cardBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardBudgetSchedule)
    (summandBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioSummandBudgetSchedule) :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            (Ω.card : ℝ) ≤ cardBudget β H n Ω v ∧
              0 ≤ summandBudget β H n Ω v ∧
              (∀ m, m ∈ Ω →
                ((finiteBoundaryGhostSourceSector m).card : ℝ) *
                    finiteBoundaryGhostBoundaryGhostMultiplicitySum n m *
                    finiteBoundaryGhostBoundaryGhostMultiplicitySum n m ≤
                  summandBudget β H n Ω v) ∧
              (cardBudget β H n Ω v * summandBudget β H n Ω v) *
                    (boundaryVertexTanhNormalizedOnePointCurrentRatioTerm
                        β H n +
                      boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
                        β H n v) +
                  boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm
                    β H n v ≤
                boundaryVertexBoxSimonCurrentRatio β n v

set_option linter.style.longLine false in


def BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardSourceMultiplicityBudgetScheduleUncutoffPositiveSubcritical
    (cardBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardBudgetSchedule)
    (sourceCardBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioSourceCardBudgetSchedule)
    (multiplicityBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryGhostMultiplicityBudgetSchedule) :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            (Ω.card : ℝ) ≤ cardBudget β H n Ω v ∧
              0 ≤ sourceCardBudget β H n Ω v ∧
              0 ≤ multiplicityBudget β H n Ω v ∧
              (∀ m, m ∈ Ω →
                ((finiteBoundaryGhostSourceSector m).card : ℝ) ≤
                  sourceCardBudget β H n Ω v) ∧
              (∀ m, m ∈ Ω →
                finiteBoundaryGhostBoundaryGhostMultiplicitySum n m ≤
                  multiplicityBudget β H n Ω v) ∧
              (cardBudget β H n Ω v *
                    (sourceCardBudget β H n Ω v *
                      multiplicityBudget β H n Ω v *
                      multiplicityBudget β H n Ω v)) *
                    (boundaryVertexTanhNormalizedOnePointCurrentRatioTerm
                        β H n +
                      boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
                        β H n v) +
                  boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm
                    β H n v ≤
                boundaryVertexBoxSimonCurrentRatio β n v

set_option linter.style.longLine false in


def BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardSourceBoundaryEdgeBudgetScheduleUncutoffPositiveSubcritical
    (cardBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardBudgetSchedule)
    (sourceCardBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioSourceCardBudgetSchedule)
    (boundaryVertexBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryVertexBudgetSchedule)
    (edgeMultiplicityBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryGhostEdgeMultiplicityBudgetSchedule) :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            (Ω.card : ℝ) ≤ cardBudget β H n Ω v ∧
              0 ≤ sourceCardBudget β H n Ω v ∧
              0 ≤ boundaryVertexBudget β H n Ω v ∧
              0 ≤ edgeMultiplicityBudget β H n Ω v ∧
              (((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ) ≤
                boundaryVertexBudget β H n Ω v) ∧
              (∀ m, m ∈ Ω →
                ((finiteBoundaryGhostSourceSector m).card : ℝ) ≤
                  sourceCardBudget β H n Ω v) ∧
              (∀ m, m ∈ Ω →
                ∀ w, w ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
                  (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ) ≤
                    edgeMultiplicityBudget β H n Ω v) ∧
              (cardBudget β H n Ω v *
                    (sourceCardBudget β H n Ω v *
                      (boundaryVertexBudget β H n Ω v *
                        edgeMultiplicityBudget β H n Ω v) *
                      (boundaryVertexBudget β H n Ω v *
                        edgeMultiplicityBudget β H n Ω v))) *
                    (boundaryVertexTanhNormalizedOnePointCurrentRatioTerm
                        β H n +
                      boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
                        β H n v) +
                  boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm
                    β H n v ≤
                boundaryVertexBoxSimonCurrentRatio β n v

set_option linter.style.longLine false in


def BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardSourceBoundaryEdgeActualBoundaryScheduleUncutoffPositiveSubcritical
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
            (Ω.card : ℝ) ≤ cardBudget β H n Ω v ∧
              0 ≤ sourceCardBudget β H n Ω v ∧
              0 ≤ edgeMultiplicityBudget β H n Ω v ∧
              (∀ m, m ∈ Ω →
                ((finiteBoundaryGhostSourceSector m).card : ℝ) ≤
                  sourceCardBudget β H n Ω v) ∧
              (∀ m, m ∈ Ω →
                ∀ w, w ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
                  (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ) ≤
                    edgeMultiplicityBudget β H n Ω v) ∧
              (cardBudget β H n Ω v *
                    (sourceCardBudget β H n Ω v *
                      (((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ) *
                          edgeMultiplicityBudget β H n Ω v) *
                      (((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ) *
                        edgeMultiplicityBudget β H n Ω v))) *
                    (boundaryVertexTanhNormalizedOnePointCurrentRatioTerm
                        β H n +
                      boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
                        β H n v) +
                  boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm
                    β H n v ≤
              boundaryVertexBoxSimonCurrentRatio β n v

set_option linter.style.longLine false in


noncomputable def
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
    (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    ℝ :=
  let cardBudget := (Ω.card : ℝ)
  let sourceCardBudget :=
    ∑ m ∈ Ω, ((finiteBoundaryGhostSourceSector m).card : ℝ)
  let edgeBudget :=
    ∑ m ∈ Ω,
      ∑ w ∈ Finset.univ.filter (FK.boxBoundary 3 n),
        (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ)
  let boundaryCard := ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ)
  cardBudget *
    (sourceCardBudget * (boundaryCard * edgeBudget) *
      (boundaryCard * edgeBudget))

set_option linter.style.longLine false in


noncomputable def
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateExactPolynomialBoundaryBudget
    (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    ℝ :=
  let cardBudget := (Ω.card : ℝ)
  let sourceCardBudget :=
    ∑ m ∈ Ω, ((finiteBoundaryGhostSourceSector m).card : ℝ)
  let edgeBudget :=
    ∑ m ∈ Ω,
      ∑ w ∈ Finset.univ.filter (FK.boxBoundary 3 n),
        (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ)
  let boundaryCard := 24 * (n : ℝ) ^ 2 + 2
  cardBudget *
    (sourceCardBudget * (boundaryCard * edgeBudget) *
      (boundaryCard * edgeBudget))

end Exact3D
end StatMech
