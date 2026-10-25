/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCriticalNewman.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianCollisionDiagonal.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianNewmanBridge.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianCriticalNewman.Part2
open Filter Topology


namespace StatMech.FrontierA

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB

noncomputable section

section FiniteTotalSpin

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem sum_pair_product
    {I J K L : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    (A : I → J → Real) (B : K → L → Real) :
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


theorem scalarFourthCumulant_finiteParityTotalSpin_eq_integrated
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real) :
    scalarFourthCumulant
        (finiteParityTotalSpinFourthMoment G beta J)
        (finiteParityTotalSpinSecondMoment G beta J) =
      ∑ i : V, finiteParityIntegratedFourthCumulant G beta J i := by
  let C : V → V → Real := fun i j =>
    expectationJ G beta J (grahamPairSupport i j)
  let Q : V → V → V → V → Real := fun i j k l =>
    expectationJ G beta J (grahamFourSupport i j k l)
  let S : Real := ∑ i : V, ∑ j : V, C i j
  have hfirst :
      (∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V, C i j * C k l) =
        S ^ 2 := by
    rw [sum_pair_product C C]
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
        rw [sum_pair_product C C]
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
        rw [sum_pair_product C C]
        ring
  unfold scalarFourthCumulant finiteParityTotalSpinFourthMoment
    finiteParityTotalSpinSecondMoment finiteParityIntegratedFourthCumulant
    finiteParityFourthUrsell
  dsimp [Q, C, S] at hfirst hsecond hthird ⊢
  simp_rw [Finset.sum_sub_distrib]
  rw [hfirst, hsecond, hthird]
  ring

end FiniteTotalSpin
end
end StatMech.FrontierA
