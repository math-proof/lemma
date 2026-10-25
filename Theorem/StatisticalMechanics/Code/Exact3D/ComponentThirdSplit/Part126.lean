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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part137
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

theorem boundaryCrossingCapSourceSectorMultiplicitySquareBound_summand_nonneg
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) :
    0 ≤
      ((finiteBoundaryGhostSourceSector m).card : ℝ) *
        finiteBoundaryGhostBoundaryGhostMultiplicitySum n m *
        finiteBoundaryGhostBoundaryGhostMultiplicitySum n m := by
  have hcard : 0 ≤ ((finiteBoundaryGhostSourceSector m).card : ℝ) :=
    Nat.cast_nonneg _
  have hmult :
      0 ≤ finiteBoundaryGhostBoundaryGhostMultiplicitySum n m :=
    finiteBoundaryGhostBoundaryGhostMultiplicitySum_nonneg (n := n) m
  exact mul_nonneg (mul_nonneg hcard hmult) hmult

set_option linter.style.longLine false in


theorem finiteBoundaryGhostBoundaryGhostMultiplicitySum_le_boundaryCard_mul_of_edgeMultiplicity_le
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    {edgeMultiplicityBudget : ℝ}
    (hedge :
      ∀ w, w ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
        (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ) ≤
          edgeMultiplicityBudget) :
    finiteBoundaryGhostBoundaryGhostMultiplicitySum n m ≤
      (((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ) *
        edgeMultiplicityBudget) := by
  classical
  unfold finiteBoundaryGhostBoundaryGhostMultiplicitySum
  have hsum :
      (∑ w ∈ Finset.univ.filter (FK.boxBoundary 3 n),
        (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ)) ≤
        ∑ _w ∈ Finset.univ.filter (FK.boxBoundary 3 n),
          edgeMultiplicityBudget := by
    exact Finset.sum_le_sum (fun w hw => hedge w hw)
  simpa [Finset.sum_const, nsmul_eq_mul] using hsum

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceSector_card_le_cutoff_sourceSector_card_sum
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
    (hm : m ∈ Ω) :
    ((finiteBoundaryGhostSourceSector m).card : ℝ) ≤
      ∑ m' ∈ Ω, ((finiteBoundaryGhostSourceSector m').card : ℝ) := by
  classical
  exact
    Finset.single_le_sum
      (fun m' _hm' =>
        (Nat.cast_nonneg (finiteBoundaryGhostSourceSector m').card : 0 ≤
          ((finiteBoundaryGhostSourceSector m').card : ℝ)))
      hm

set_option linter.style.longLine false in


theorem finiteBoundaryGhostBoundaryEdgeMultiplicity_le_cutoff_boundaryEdge_sum
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ}
    (hm : m ∈ Ω)
    {w : FK.boxVerts 3 n}
    (hw : w ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ) ≤
      ∑ m' ∈ Ω,
        ∑ w' ∈ Finset.univ.filter (FK.boxBoundary 3 n),
          (m' (finiteBoundaryGhostBoundaryEdge n w') : ℝ) := by
  classical
  have hinner :
      (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ) ≤
        ∑ w' ∈ Finset.univ.filter (FK.boxBoundary 3 n),
          (m (finiteBoundaryGhostBoundaryEdge n w') : ℝ) := by
    exact
      Finset.single_le_sum
        (fun w' _hw' =>
          (Nat.cast_nonneg (m (finiteBoundaryGhostBoundaryEdge n w')) :
            0 ≤ (m (finiteBoundaryGhostBoundaryEdge n w') : ℝ)))
        hw
  have houter :
      (∑ w' ∈ Finset.univ.filter (FK.boxBoundary 3 n),
          (m (finiteBoundaryGhostBoundaryEdge n w') : ℝ)) ≤
        ∑ m' ∈ Ω,
          ∑ w' ∈ Finset.univ.filter (FK.boxBoundary 3 n),
            (m' (finiteBoundaryGhostBoundaryEdge n w') : ℝ) := by
    exact
      Finset.single_le_sum
        (fun m' _hm' =>
          Finset.sum_nonneg
            (fun w' _hw' =>
              (Nat.cast_nonneg (m' (finiteBoundaryGhostBoundaryEdge n w')) :
                0 ≤ (m' (finiteBoundaryGhostBoundaryEdge n w') : ℝ))))
        hm
  exact le_trans hinner houter

set_option linter.style.longLine false in


theorem boundaryCrossingCapSourceSectorMultiplicitySquareBound_summand_le_sourceCard_mul_multiplicityBudget_sq
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    {sourceCardBudget multiplicityBudget : ℝ}
    (hsource :
      ((finiteBoundaryGhostSourceSector m).card : ℝ) ≤ sourceCardBudget)
    (hmult :
      finiteBoundaryGhostBoundaryGhostMultiplicitySum n m ≤
        multiplicityBudget)
    (hsourceBudgetNonneg : 0 ≤ sourceCardBudget)
    (hmultBudgetNonneg : 0 ≤ multiplicityBudget) :
    ((finiteBoundaryGhostSourceSector m).card : ℝ) *
        finiteBoundaryGhostBoundaryGhostMultiplicitySum n m *
        finiteBoundaryGhostBoundaryGhostMultiplicitySum n m ≤
      sourceCardBudget * multiplicityBudget * multiplicityBudget := by
  have hmultNonneg :
      0 ≤ finiteBoundaryGhostBoundaryGhostMultiplicitySum n m :=
    finiteBoundaryGhostBoundaryGhostMultiplicitySum_nonneg (n := n) m
  have hcardMul :
      ((finiteBoundaryGhostSourceSector m).card : ℝ) *
          finiteBoundaryGhostBoundaryGhostMultiplicitySum n m ≤
        sourceCardBudget * multiplicityBudget := by
    exact
      mul_le_mul hsource hmult hmultNonneg hsourceBudgetNonneg
  have hbudgetMulNonneg : 0 ≤ sourceCardBudget * multiplicityBudget :=
    mul_nonneg hsourceBudgetNonneg hmultBudgetNonneg
  exact
    mul_le_mul hcardMul hmult hmultNonneg hbudgetMulNonneg

set_option linter.style.longLine false in


theorem boundaryCrossingCapSourceSectorMultiplicitySquareBound_singleton
    (β H : ℝ) {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) :
    boundaryCrossingCapSourceSectorMultiplicitySquareBound β H n
        ({m} : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) =
      ((finiteBoundaryGhostSourceSector m).card : ℝ) *
        finiteBoundaryGhostBoundaryGhostMultiplicitySum n m *
        finiteBoundaryGhostBoundaryGhostMultiplicitySum n m := by
  classical
  simp [boundaryCrossingCapSourceSectorMultiplicitySquareBound]

set_option linter.style.longLine false in

theorem boundaryCrossingCapSourceSectorMultiplicitySquareBound_nonneg
    (β H : ℝ) {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    0 ≤ boundaryCrossingCapSourceSectorMultiplicitySquareBound β H n Ω := by
  classical
  unfold boundaryCrossingCapSourceSectorMultiplicitySquareBound
  exact
    Finset.sum_nonneg
      (fun m _hm =>
        boundaryCrossingCapSourceSectorMultiplicitySquareBound_summand_nonneg
          (n := n) m)

set_option linter.style.longLine false in


theorem boundaryCrossingCapSourceSectorMultiplicitySquareBound_mono
    (β H : ℝ) {n : ℕ}
    {Ω Ω' : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    (hΩ : Ω ⊆ Ω') :
    boundaryCrossingCapSourceSectorMultiplicitySquareBound β H n Ω ≤
      boundaryCrossingCapSourceSectorMultiplicitySquareBound β H n Ω' := by
  classical
  unfold boundaryCrossingCapSourceSectorMultiplicitySquareBound
  exact
    Finset.sum_le_sum_of_subset_of_nonneg hΩ
      (fun m _hm _hnot =>
        boundaryCrossingCapSourceSectorMultiplicitySquareBound_summand_nonneg
          (n := n) m)

set_option linter.style.longLine false in


theorem boundaryCrossingCapSourceSectorMultiplicitySquareBound_le_card_mul_of_summand_le
    (β H : ℝ) {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {M : ℝ}
    (hM : ∀ m, m ∈ Ω →
      ((finiteBoundaryGhostSourceSector m).card : ℝ) *
          finiteBoundaryGhostBoundaryGhostMultiplicitySum n m *
          finiteBoundaryGhostBoundaryGhostMultiplicitySum n m ≤
        M) :
    boundaryCrossingCapSourceSectorMultiplicitySquareBound β H n Ω ≤
      (Ω.card : ℝ) * M := by
  classical
  unfold boundaryCrossingCapSourceSectorMultiplicitySquareBound
  have hsum :
      (∑ m ∈ Ω,
        ((finiteBoundaryGhostSourceSector m).card : ℝ) *
          finiteBoundaryGhostBoundaryGhostMultiplicitySum n m *
          finiteBoundaryGhostBoundaryGhostMultiplicitySum n m) ≤
        ∑ _m ∈ Ω, M := by
    exact Finset.sum_le_sum (fun m hm => hM m hm)
  simpa [Finset.sum_const, nsmul_eq_mul] using hsum

set_option linter.style.longLine false in


theorem boundaryCrossingCapSourceSectorMultiplicitySquareBound_weightNonzeroCutoff_le
    (β H : ℝ) {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    boundaryCrossingCapSourceSectorMultiplicitySquareBound β H n
        (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω) ≤
      boundaryCrossingCapSourceSectorMultiplicitySquareBound β H n Ω := by
  refine boundaryCrossingCapSourceSectorMultiplicitySquareBound_mono β H ?_
  intro m hm
  exact (finiteBoundaryGhostWeightNonzeroCutoff_mem.mp hm).1

set_option linter.style.longLine false in


theorem
    finiteBoundaryGhostCollapsedCutoffBoundaryFiberBoundaryCrossingPairCountMultiplicityCap_le_sourceSectorMultiplicitySquare
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    finiteBoundaryGhostCollapsedCutoffBoundaryFiberBoundaryCrossingPairCountMultiplicityCap
        n Ω ≤
      ∑ m ∈ Ω,
        ((finiteBoundaryGhostSourceSector m).card : ℝ) *
          finiteBoundaryGhostBoundaryGhostMultiplicitySum n m *
          finiteBoundaryGhostBoundaryGhostMultiplicitySum n m := by
  classical
  unfold
    finiteBoundaryGhostCollapsedCutoffBoundaryFiberBoundaryCrossingPairCountMultiplicityCap
  refine Finset.sum_le_sum ?_
  intro m _hm
  have hsum :
      (∑ w ∈ Finset.univ.filter (fun w : FK.boxVerts 3 n =>
          FK.boxBoundary 3 n w),
        (finiteBoundaryGhostBoundaryCrossingPairCount m w : ℝ)) ≤
        ((finiteBoundaryGhostSourceSector m).card : ℝ) *
          finiteBoundaryGhostBoundaryGhostMultiplicitySum n m := by
    calc
      (∑ w ∈ Finset.univ.filter (fun w : FK.boxVerts 3 n =>
          FK.boxBoundary 3 n w),
        (finiteBoundaryGhostBoundaryCrossingPairCount m w : ℝ)) ≤
          ∑ w ∈ Finset.univ.filter (fun w : FK.boxVerts 3 n =>
              FK.boxBoundary 3 n w),
            ((finiteBoundaryGhostSourceSector m).card : ℝ) *
              (m (finiteBoundaryGhostBoundaryEdge n w) : ℝ) := by
        refine Finset.sum_le_sum ?_
        intro w _hw
        have hnat :=
          finiteBoundaryGhostBoundaryCrossingPairCount_le_sourceSector_card_mul_boundaryGhostMultiplicity
            m w
        have hreal :
            (finiteBoundaryGhostBoundaryCrossingPairCount m w : ℝ) ≤
              (((finiteBoundaryGhostSourceSector m).card *
                m (finiteBoundaryGhostBoundaryEdge n w) : ℕ) : ℝ) := by
          exact_mod_cast (by
            simpa [finiteBoundaryGhostBoundaryEdge] using hnat)
        simpa [Nat.cast_mul] using hreal
      _ =
          ((finiteBoundaryGhostSourceSector m).card : ℝ) *
            finiteBoundaryGhostBoundaryGhostMultiplicitySum n m := by
        unfold finiteBoundaryGhostBoundaryGhostMultiplicitySum
        rw [Finset.mul_sum]
  have hmul :=
    mul_le_mul_of_nonneg_right hsum
      (finiteBoundaryGhostBoundaryGhostMultiplicitySum_nonneg (n := n) m)
  simpa [mul_assoc] using hmul


end Exact3D
end StatMech
