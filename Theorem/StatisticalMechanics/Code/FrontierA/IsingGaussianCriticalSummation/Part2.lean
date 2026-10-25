/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCriticalSummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalCubeInfrared
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianIndependentDisentangling.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianCriticalSummation.Part2
open Filter Finset Set Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB

noncomputable section

variable {d : Nat}


section FiniteTree

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem finitePairCorrelation_nonneg
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (x y : V) :
    0 ≤ expectationJ G beta J (grahamPairSupport x y) := by
  rw [current_representation]
  exact div_nonneg
    (StatMech.Ising.acr_currentSum_nonneg G beta J hbeta hJ _)
    (StatMech.Ising.acr_currentSum_nonneg G beta J hbeta hJ _)

theorem finiteCurrentTreeDiagram_nonneg
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (i j k l : V) :
    0 ≤ finiteCurrentTreeDiagram G beta J i j k l := by
  unfold finiteCurrentTreeDiagram
  exact Finset.sum_nonneg fun y _ => by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (finitePairCorrelation_nonneg G beta J hbeta hJ i y)
          (finitePairCorrelation_nonneg G beta J hbeta hJ j y))
        (finitePairCorrelation_nonneg G beta J hbeta hJ k y))
      (finitePairCorrelation_nonneg G beta J hbeta hJ l y)

omit [DecidableEq V] in
theorem finite_sum_three_mul
    (a : Real) (A B C : V → Real) :
    (∑ j : V, ∑ k : V, ∑ l : V, a * A j * B k * C l) =
      a * (∑ j : V, A j) * (∑ k : V, B k) * (∑ l : V, C l) := by
  calc
    _ = ∑ j : V, ∑ k : V,
        (a * A j * B k) * (∑ l : V, C l) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
    _ = ∑ j : V,
        (a * A j) * (∑ k : V, B k) * (∑ l : V, C l) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ = a * (∑ j : V, A j) * (∑ k : V, B k) *
        (∑ l : V, C l) := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      rw [show (∑ j : V, a * A j) = a * (∑ j : V, A j) by
        rw [Finset.mul_sum]]

set_option maxHeartbeats 2000000 in


theorem finiteDistinctIntegratedFourthCumulant_treeDiagram_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (chi : Real) (hchi : 0 ≤ chi)
    (hrow : ∀ y : V,
      ∑ x : V, expectationJ G beta J (grahamPairSupport x y) ≤ chi)
    (i : V) :
    0 ≤ -finiteDistinctIntegratedFourthCumulant G beta J i ∧
      -finiteDistinctIntegratedFourthCumulant G beta J i ≤ 2 * chi ^ 4 := by
  let C : V → V → Real := fun x y =>
    expectationJ G beta J (grahamPairSupport x y)
  have hC (x y : V) : 0 ≤ C x y :=
    finitePairCorrelation_nonneg G beta J hbeta hJ x y
  have hpoint (j k l : V) :
      0 ≤ -(if i ≠ j ∧ i ≠ k ∧ i ≠ l ∧
          j ≠ k ∧ j ≠ l ∧ k ≠ l then
        finiteIsingFourthUrsell G beta J i j k l else 0) ∧
      -(if i ≠ j ∧ i ≠ k ∧ i ≠ l ∧
          j ≠ k ∧ j ≠ l ∧ k ≠ l then
        finiteIsingFourthUrsell G beta J i j k l else 0) ≤
        2 * finiteCurrentTreeDiagram G beta J i j k l := by
    by_cases h : i ≠ j ∧ i ≠ k ∧ i ≠ l ∧
        j ≠ k ∧ j ≠ l ∧ k ≠ l
    · simp only [if_pos h]
      exact finiteIsing_treeDiagram_bound G beta J hbeta hJ
        h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
    · simp only [if_neg h, neg_zero]
      exact ⟨le_rfl, mul_nonneg (by norm_num)
        (finiteCurrentTreeDiagram_nonneg G beta J hbeta hJ i j k l)⟩
  have hnonneg :
      0 ≤ ∑ j : V, ∑ k : V, ∑ l : V,
        -(if i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l then
          finiteIsingFourthUrsell G beta J i j k l else 0) :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ =>
      Finset.sum_nonneg fun l _ => (hpoint j k l).1
  have hupper :
      (∑ j : V, ∑ k : V, ∑ l : V,
        -(if i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l then
          finiteIsingFourthUrsell G beta J i j k l else 0)) ≤
      ∑ j : V, ∑ k : V, ∑ l : V,
        2 * finiteCurrentTreeDiagram G beta J i j k l :=
    Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ =>
      Finset.sum_le_sum fun l _ => (hpoint j k l).2
  have hreorder :
      (∑ j : V, ∑ k : V, ∑ l : V,
          2 * finiteCurrentTreeDiagram G beta J i j k l) =
        2 * ∑ y : V, C i y *
          (∑ x : V, C x y) ^ 3 := by
    unfold finiteCurrentTreeDiagram C
    calc
      _ = 2 * ∑ j : V, ∑ k : V, ∑ l : V, ∑ y : V,
          expectationJ G beta J (grahamPairSupport i y) *
          expectationJ G beta J (grahamPairSupport j y) *
          expectationJ G beta J (grahamPairSupport k y) *
          expectationJ G beta J (grahamPairSupport l y) := by
        simp_rw [Finset.mul_sum]
      _ = 2 * ∑ y : V, ∑ j : V, ∑ k : V, ∑ l : V,
          expectationJ G beta J (grahamPairSupport i y) *
          expectationJ G beta J (grahamPairSupport j y) *
          expectationJ G beta J (grahamPairSupport k y) *
          expectationJ G beta J (grahamPairSupport l y) := by
        congr 1
        calc
          _ = ∑ j : V, ∑ k : V, ∑ y : V, ∑ l : V,
              expectationJ G beta J (grahamPairSupport i y) *
              expectationJ G beta J (grahamPairSupport j y) *
              expectationJ G beta J (grahamPairSupport k y) *
              expectationJ G beta J (grahamPairSupport l y) := by
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_comm]
          _ = ∑ j : V, ∑ y : V, ∑ k : V, ∑ l : V,
              expectationJ G beta J (grahamPairSupport i y) *
              expectationJ G beta J (grahamPairSupport j y) *
              expectationJ G beta J (grahamPairSupport k y) *
              expectationJ G beta J (grahamPairSupport l y) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_comm]
          _ = _ := by rw [Finset.sum_comm]
      _ = 2 * ∑ y : V, C i y * (∑ x : V, C x y) ^ 3 := by
        congr 1
        apply Finset.sum_congr rfl
        intro y _
        rw [finite_sum_three_mul]
        ring
  have hdiagram :
      2 * ∑ y : V, C i y * (∑ x : V, C x y) ^ 3 ≤
        2 * chi ^ 4 := by
    have hsum :
        ∑ y : V, C i y * (∑ x : V, C x y) ^ 3 ≤
          ∑ y : V, C i y * chi ^ 3 := by
      apply Finset.sum_le_sum
      intro y _
      apply mul_le_mul_of_nonneg_left _ (hC i y)
      exact pow_le_pow_left₀
        (Finset.sum_nonneg fun x _ => hC x y) (hrow y) 3
    have hsymm (x y : V) : C x y = C y x := by
      dsimp [C]
      unfold grahamPairSupport
      rw [symmDiff_comm]
    have hrowi : ∑ y : V, C i y ≤ chi := by
      calc
        ∑ y : V, C i y = ∑ y : V, C y i := by
          apply Finset.sum_congr rfl
          intro y _
          exact hsymm i y
        _ ≤ chi := hrow i
    calc
      2 * ∑ y : V, C i y * (∑ x : V, C x y) ^ 3 ≤
          2 * ∑ y : V, C i y * chi ^ 3 := by gcongr
      _ = 2 * (∑ y : V, C i y) * chi ^ 3 := by
        rw [← Finset.sum_mul]
        ring
      _ ≤ 2 * chi * chi ^ 3 := by
        gcongr
      _ = 2 * chi ^ 4 := by ring
  have hneg :
      (∑ j : V, ∑ k : V, ∑ l : V,
        -(if i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l then
          finiteIsingFourthUrsell G beta J i j k l else 0)) =
        -finiteDistinctIntegratedFourthCumulant G beta J i := by
    simp [finiteDistinctIntegratedFourthCumulant]
  rw [hneg] at hnonneg hupper
  exact ⟨hnonneg, hupper.trans (hreorder.le.trans hdiagram)⟩

end FiniteTree
end
end StatMech.FrontierA
