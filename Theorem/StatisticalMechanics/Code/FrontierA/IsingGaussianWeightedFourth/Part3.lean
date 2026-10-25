/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedFourth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianCriticalNewman.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianConePolarization.Part4
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianWeightedFourth.Part2
open Filter Finset Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem weighted_sum_pair_product
    {I J K L : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    (A : I -> J -> Real) (B : K -> L -> Real) :
    (∑ i : I, ∑ j : J, ∑ k : K, ∑ l : L, A i j * B k l) =
      (∑ i : I, ∑ j : J, A i j) * (∑ k : K, ∑ l : L, B k l) := by
  calc
    _ = ∑ i : I, ∑ j : J, A i j * (∑ k : K, ∑ l : L, B k l) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
    _ = ∑ i : I, (∑ j : J, A i j) * (∑ k : K, ∑ l : L, B k l) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
    _ = _ := by rw [Finset.sum_mul]


theorem scalarFourthCumulant_finiteWeightedParity_eq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (a : V -> Real) :
    scalarFourthCumulant
        (finiteWeightedParityFourthMoment G beta J a)
        (finiteWeightedParitySecondMoment G beta J a) =
      finiteWeightedParityFourthCumulant G beta J a := by
  let C : V -> V -> Real := fun i j =>
    a i * a j * expectationJ G beta J (grahamPairSupport i j)
  let S : Real := ∑ i : V, ∑ j : V, C i j
  have hfirst :
      (∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V, C i j * C k l) =
        S ^ 2 := by
    rw [weighted_sum_pair_product C C]
    ring
  have hsecond :
      (∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V, C i k * C j l) =
        S ^ 2 := by
    calc
      _ = ∑ i : V, ∑ k : V, ∑ j : V, ∑ l : V,
          C i k * C j l := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = S ^ 2 := by
        rw [weighted_sum_pair_product C C]
        ring
  have hthird :
      (∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V, C i l * C j k) =
        S ^ 2 := by
    calc
      _ = ∑ i : V, ∑ j : V, ∑ l : V, ∑ k : V,
          C i l * C j k := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_comm]
      _ = ∑ i : V, ∑ l : V, ∑ j : V, ∑ k : V,
          C i l * C j k := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = S ^ 2 := by
        rw [weighted_sum_pair_product C C]
        ring
  have hfirstExpanded :
      (∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V,
        a i * a j * a k * a l *
          (expectationJ G beta J (grahamPairSupport i j) *
            expectationJ G beta J (grahamPairSupport k l))) = S ^ 2 := by
    calc
      _ = ∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V,
          C i j * C k l := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro l _
        dsimp [C]
        ring
      _ = S ^ 2 := hfirst
  have hsecondExpanded :
      (∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V,
        a i * a j * a k * a l *
          (expectationJ G beta J (grahamPairSupport i k) *
            expectationJ G beta J (grahamPairSupport j l))) = S ^ 2 := by
    calc
      _ = ∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V,
          C i k * C j l := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro l _
        dsimp [C]
        ring
      _ = S ^ 2 := hsecond
  have hthirdExpanded :
      (∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V,
        a i * a j * a k * a l *
          (expectationJ G beta J (grahamPairSupport i l) *
            expectationJ G beta J (grahamPairSupport j k))) = S ^ 2 := by
    calc
      _ = ∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V,
          C i l * C j k := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro l _
        dsimp [C]
        ring
      _ = S ^ 2 := hthird
  unfold scalarFourthCumulant finiteWeightedParityFourthMoment
    finiteWeightedParitySecondMoment finiteWeightedParityFourthCumulant
    finiteParityFourthUrsell
  dsimp [C, S] at hfirstExpanded hsecondExpanded hthirdExpanded ⊢
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [hfirstExpanded, hsecondExpanded, hthirdExpanded]
  ring

end
end StatMech.FrontierA
