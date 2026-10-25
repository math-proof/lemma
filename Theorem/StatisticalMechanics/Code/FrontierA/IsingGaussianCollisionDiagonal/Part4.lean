/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCollisionDiagonal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianCriticalSummation.Part5
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianCollisionDiagonal.Part4
open Filter Finset Set Topology
open scoped BigOperators symmDiff


namespace StatMech.FrontierA

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem neg_finiteParityIntegratedFourthCumulant_eq_distinct_add_collision
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real) (i : V) :
    -finiteParityIntegratedFourthCumulant G beta J i =
      -finiteDistinctIntegratedFourthCumulant G beta J i +
        finiteCollisionIntegratedFourthCumulant G beta J i := by
  unfold finiteParityIntegratedFourthCumulant
    finiteDistinctIntegratedFourthCumulant
    finiteCollisionIntegratedFourthCumulant
  simp_rw [← Finset.sum_neg_distrib]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  by_cases h : i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l
  · rw [finiteCollisionFourthWeight, if_pos h, if_pos h, add_zero]
    exact congrArg Neg.neg
      (finiteParityFourthUrsell_eq_finiteIsing_of_distinct
        G beta J h.1 h.2.1 h.2.2.1 h.2.2.2.1
          h.2.2.2.2.1 h.2.2.2.2.2)
  · rw [finiteCollisionFourthWeight, if_neg h, if_neg h]
    ring


theorem finiteParityIntegratedFourthCumulant_treeDiagram_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (chi : Real) (hchi : 0 ≤ chi)
    (hrow : ∀ y : V,
      ∑ x : V, expectationJ G beta J (grahamPairSupport x y) ≤ chi)
    (i : V) :
    0 ≤ -finiteParityIntegratedFourthCumulant G beta J i ∧
      -finiteParityIntegratedFourthCumulant G beta J i ≤
        2 * chi ^ 4 + 12 * chi ^ 2 := by
  have hdist := finiteDistinctIntegratedFourthCumulant_treeDiagram_bound
    G beta J hbeta hJ chi hchi hrow i
  have hcollision := finiteCollisionIntegratedFourthCumulant_le
    G beta J hbeta hJ chi hchi hrow i
  rw [neg_finiteParityIntegratedFourthCumulant_eq_distinct_add_collision]
  exact ⟨add_nonneg hdist.1 hcollision.1,
    add_le_add hdist.2 hcollision.2⟩

end
end StatMech.FrontierA
