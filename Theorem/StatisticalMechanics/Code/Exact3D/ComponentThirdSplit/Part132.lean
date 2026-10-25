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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part145
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget_eventually_le_polynomialBoundaryBudget :
    ∀ᶠ n in atTop,
      ∀ Ω : Finset
        (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
        boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
            n Ω ≤
          boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregatePolynomialBoundaryBudget
            n Ω := by
  filter_upwards [boxBoundaryCard3_eventually_le_26_mul_sq] with n hboundary
  intro Ω
  let cardBudget := (Ω.card : ℝ)
  let sourceCardBudget :=
    ∑ m ∈ Ω, ((finiteBoundaryGhostSourceSector m).card : ℝ)
  let edgeBudget :=
    ∑ m ∈ Ω,
      ∑ w ∈ Finset.univ.filter (FK.boxBoundary 3 n),
        (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ)
  let actualBoundaryCard :=
    ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ)
  let polynomialBoundaryCard := 26 * (n : ℝ) ^ 2
  have hcardNonneg : 0 ≤ cardBudget := by
    simp [cardBudget]
  have hsourceNonneg : 0 ≤ sourceCardBudget := by
    simpa [sourceCardBudget] using
      (Finset.sum_nonneg (fun m _hm => Nat.cast_nonneg _) :
        0 ≤ ∑ m ∈ Ω, ((finiteBoundaryGhostSourceSector m).card : ℝ))
  have hedgeNonneg : 0 ≤ edgeBudget := by
    simpa [edgeBudget] using
      (Finset.sum_nonneg
        (fun m _hm =>
          Finset.sum_nonneg
            (fun w _hw =>
              (Nat.cast_nonneg (m (finiteBoundaryGhostBoundaryEdge n w)) :
                0 ≤ (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ)))) :
        0 ≤ ∑ m ∈ Ω,
          ∑ w ∈ Finset.univ.filter (FK.boxBoundary 3 n),
            (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ))
  have hactualBoundaryNonneg : 0 ≤ actualBoundaryCard := by
    simp [actualBoundaryCard]
  have hpolynomialBoundaryNonneg : 0 ≤ polynomialBoundaryCard := by
    dsimp [polynomialBoundaryCard]
    nlinarith [sq_nonneg (n : ℝ)]
  have hboundaryLe :
      actualBoundaryCard ≤ polynomialBoundaryCard := by
    simpa [actualBoundaryCard, polynomialBoundaryCard] using hboundary
  have hmultiplicityLe :
      actualBoundaryCard * edgeBudget ≤
        polynomialBoundaryCard * edgeBudget :=
    mul_le_mul_of_nonneg_right hboundaryLe hedgeNonneg
  have hactualMultiplicityNonneg :
      0 ≤ actualBoundaryCard * edgeBudget :=
    mul_nonneg hactualBoundaryNonneg hedgeNonneg
  have hpolynomialMultiplicityNonneg :
      0 ≤ polynomialBoundaryCard * edgeBudget :=
    mul_nonneg hpolynomialBoundaryNonneg hedgeNonneg
  have hsourceMultiplicityLe :
      sourceCardBudget * (actualBoundaryCard * edgeBudget) ≤
        sourceCardBudget * (polynomialBoundaryCard * edgeBudget) :=
    mul_le_mul_of_nonneg_left hmultiplicityLe hsourceNonneg
  have hsourcePolynomialMultiplicityNonneg :
      0 ≤ sourceCardBudget * (polynomialBoundaryCard * edgeBudget) :=
    mul_nonneg hsourceNonneg hpolynomialMultiplicityNonneg
  have hinner :
      sourceCardBudget * (actualBoundaryCard * edgeBudget) *
          (actualBoundaryCard * edgeBudget) ≤
        sourceCardBudget * (polynomialBoundaryCard * edgeBudget) *
          (polynomialBoundaryCard * edgeBudget) :=
    mul_le_mul hsourceMultiplicityLe hmultiplicityLe
      hactualMultiplicityNonneg hsourcePolynomialMultiplicityNonneg
  have htotal :
      cardBudget *
          (sourceCardBudget * (actualBoundaryCard * edgeBudget) *
            (actualBoundaryCard * edgeBudget)) ≤
        cardBudget *
          (sourceCardBudget * (polynomialBoundaryCard * edgeBudget) *
            (polynomialBoundaryCard * edgeBudget)) :=
    mul_le_mul_of_nonneg_left hinner hcardNonneg
  simpa [
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget,
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregatePolynomialBoundaryBudget,
    cardBudget, sourceCardBudget, edgeBudget, actualBoundaryCard,
    polynomialBoundaryCard] using htotal

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget_le_cardSourceBoundaryEdgeBudget
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {cardBudget sourceCardBudget edgeMultiplicityBudget : ℝ}
    (hcard : (Ω.card : ℝ) ≤ cardBudget)
    (hsource :
      (∑ m ∈ Ω, ((finiteBoundaryGhostSourceSector m).card : ℝ)) ≤
        sourceCardBudget)
    (hsourceNonneg : 0 ≤ sourceCardBudget)
    (hedge :
      (∑ m ∈ Ω,
        ∑ w ∈ Finset.univ.filter (FK.boxBoundary 3 n),
          (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ)) ≤
        edgeMultiplicityBudget)
    (hedgeNonneg : 0 ≤ edgeMultiplicityBudget) :
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
        n Ω ≤
      cardBudget *
        (sourceCardBudget *
          (((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ) *
            edgeMultiplicityBudget) *
          (((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ) *
            edgeMultiplicityBudget)) := by
  let actualCard := (Ω.card : ℝ)
  let actualSource :=
    ∑ m ∈ Ω, ((finiteBoundaryGhostSourceSector m).card : ℝ)
  let actualEdge :=
    ∑ m ∈ Ω,
      ∑ w ∈ Finset.univ.filter (FK.boxBoundary 3 n),
        (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ)
  let boundaryCard := ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ)
  let actualBoundaryEdge := boundaryCard * actualEdge
  let budgetBoundaryEdge := boundaryCard * edgeMultiplicityBudget
  have hactualCardNonneg : 0 ≤ actualCard := by
    simp [actualCard]
  have hcardBudgetNonneg : 0 ≤ cardBudget :=
    le_trans hactualCardNonneg (by simpa [actualCard] using hcard)
  have hactualSourceNonneg : 0 ≤ actualSource := by
    simpa [actualSource] using
      (Finset.sum_nonneg (fun m _hm => Nat.cast_nonneg _) :
        0 ≤ ∑ m ∈ Ω, ((finiteBoundaryGhostSourceSector m).card : ℝ))
  have hactualEdgeNonneg : 0 ≤ actualEdge := by
    simpa [actualEdge] using
      (Finset.sum_nonneg
        (fun m _hm =>
          Finset.sum_nonneg
            (fun w _hw =>
              (Nat.cast_nonneg (m (finiteBoundaryGhostBoundaryEdge n w)) :
                0 ≤ (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ)))) :
        0 ≤ ∑ m ∈ Ω,
          ∑ w ∈ Finset.univ.filter (FK.boxBoundary 3 n),
            (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ))
  have hboundaryCardNonneg : 0 ≤ boundaryCard := by
    simp [boundaryCard]
  have hactualBoundaryEdgeNonneg : 0 ≤ actualBoundaryEdge :=
    mul_nonneg hboundaryCardNonneg hactualEdgeNonneg
  have hbudgetBoundaryEdgeNonneg : 0 ≤ budgetBoundaryEdge :=
    mul_nonneg hboundaryCardNonneg hedgeNonneg
  have hedgeBoundary :
      actualBoundaryEdge ≤ budgetBoundaryEdge := by
    exact mul_le_mul_of_nonneg_left
      (by simpa [actualEdge] using hedge) hboundaryCardNonneg
  have hsourceBoundary :
      actualSource * actualBoundaryEdge ≤
        sourceCardBudget * budgetBoundaryEdge :=
    mul_le_mul
      (by simpa [actualSource] using hsource)
      hedgeBoundary hactualBoundaryEdgeNonneg hsourceNonneg
  have hsourceBudgetBoundaryNonneg :
      0 ≤ sourceCardBudget * budgetBoundaryEdge :=
    mul_nonneg hsourceNonneg hbudgetBoundaryEdgeNonneg
  have hsourceBoundarySquare :
      actualSource * actualBoundaryEdge * actualBoundaryEdge ≤
        sourceCardBudget * budgetBoundaryEdge * budgetBoundaryEdge :=
    mul_le_mul hsourceBoundary hedgeBoundary hactualBoundaryEdgeNonneg
      hsourceBudgetBoundaryNonneg
  have hactualSummandNonneg :
      0 ≤ actualSource * actualBoundaryEdge * actualBoundaryEdge :=
    mul_nonneg
      (mul_nonneg hactualSourceNonneg hactualBoundaryEdgeNonneg)
      hactualBoundaryEdgeNonneg
  have hfinal :
      actualCard *
          (actualSource * actualBoundaryEdge * actualBoundaryEdge) ≤
        cardBudget *
          (sourceCardBudget * budgetBoundaryEdge * budgetBoundaryEdge) :=
    mul_le_mul
      (by simpa [actualCard] using hcard)
      hsourceBoundarySquare hactualSummandNonneg hcardBudgetNonneg
  simpa [
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget,
    actualCard, actualSource, actualEdge, boundaryCard, actualBoundaryEdge,
    budgetBoundaryEdge, mul_assoc] using hfinal

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBound_le_aggregateActualBoundaryBudget
    (β H : ℝ) {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    boundaryCrossingCapSourceSectorMultiplicitySquareBound β H n Ω ≤
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
        n Ω := by
  let cardBudget := (Ω.card : ℝ)
  let sourceCardBudget :=
    ∑ m ∈ Ω, ((finiteBoundaryGhostSourceSector m).card : ℝ)
  let edgeBudget :=
    ∑ m ∈ Ω,
      ∑ w ∈ Finset.univ.filter (FK.boxBoundary 3 n),
        (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ)
  let boundaryCard := ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ)
  let multiplicityBudget := boundaryCard * edgeBudget
  let summandBudget :=
    sourceCardBudget * multiplicityBudget * multiplicityBudget
  have hsourceBudgetNonneg : 0 ≤ sourceCardBudget := by
    simpa [sourceCardBudget] using
      (Finset.sum_nonneg (fun m _hm => Nat.cast_nonneg _) :
        0 ≤ ∑ m ∈ Ω, ((finiteBoundaryGhostSourceSector m).card : ℝ))
  have hedgeBudgetNonneg : 0 ≤ edgeBudget := by
    simpa [edgeBudget] using
      (Finset.sum_nonneg
        (fun m _hm =>
          Finset.sum_nonneg
            (fun w _hw =>
              (Nat.cast_nonneg (m (finiteBoundaryGhostBoundaryEdge n w)) :
                0 ≤ (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ)))) :
        0 ≤ ∑ m ∈ Ω,
          ∑ w ∈ Finset.univ.filter (FK.boxBoundary 3 n),
            (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ))
  have hboundaryCardNonneg : 0 ≤ boundaryCard := by
    simp [boundaryCard]
  have hmultiplicityBudgetNonneg : 0 ≤ multiplicityBudget :=
    mul_nonneg hboundaryCardNonneg hedgeBudgetNonneg
  have hsummand :
      ∀ m, m ∈ Ω →
        ((finiteBoundaryGhostSourceSector m).card : ℝ) *
            finiteBoundaryGhostBoundaryGhostMultiplicitySum n m *
            finiteBoundaryGhostBoundaryGhostMultiplicitySum n m ≤
          summandBudget := by
    intro m hm
    have hsource :
        ((finiteBoundaryGhostSourceSector m).card : ℝ) ≤
          sourceCardBudget := by
      simpa [sourceCardBudget] using
        finiteBoundaryGhostSourceSector_card_le_cutoff_sourceSector_card_sum
          (n := n) (Ω := Ω) (m := m) hm
    have hedge :
        ∀ w, w ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
          (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ) ≤
            edgeBudget := by
      intro w hw
      simpa [edgeBudget] using
        finiteBoundaryGhostBoundaryEdgeMultiplicity_le_cutoff_boundaryEdge_sum
          (n := n) (Ω := Ω) (m := m) hm (w := w) hw
    have hmult :
        finiteBoundaryGhostBoundaryGhostMultiplicitySum n m ≤
          multiplicityBudget := by
      have hsum :=
        finiteBoundaryGhostBoundaryGhostMultiplicitySum_le_boundaryCard_mul_of_edgeMultiplicity_le
          (n := n) m hedge
      simpa [boundaryCard, multiplicityBudget] using hsum
    simpa [summandBudget] using
      boundaryCrossingCapSourceSectorMultiplicitySquareBound_summand_le_sourceCard_mul_multiplicityBudget_sq
        (n := n) m hsource hmult hsourceBudgetNonneg
        hmultiplicityBudgetNonneg
  have hcard :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBound_le_card_mul_of_summand_le
      (β := β) (H := H) (Ω := Ω) hsummand
  have hcard' :
      boundaryCrossingCapSourceSectorMultiplicitySquareBound β H n Ω ≤
        cardBudget * summandBudget := by
    simpa [cardBudget] using hcard
  change
    boundaryCrossingCapSourceSectorMultiplicitySquareBound β H n Ω ≤
      cardBudget *
        (sourceCardBudget * (boundaryCard * edgeBudget) *
          (boundaryCard * edgeBudget))
  simpa [summandBudget, multiplicityBudget] using hcard'

end Exact3D
end StatMech
