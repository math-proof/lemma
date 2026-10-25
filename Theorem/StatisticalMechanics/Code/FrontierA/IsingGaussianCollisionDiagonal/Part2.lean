/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCollisionDiagonal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianCriticalSummation.Part5
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianCollisionDiagonal.Part2
open Filter Finset Set Topology
open scoped BigOperators symmDiff


namespace StatMech.FrontierA

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem finiteCollisionFourthWeight_nonneg_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) (i j k l : V) :
    0 ≤ finiteCollisionFourthWeight G beta J i j k l ∧
      finiteCollisionFourthWeight G beta J i j k l ≤
        finiteCollisionFourthMajorant G beta J i j k l := by
  have hC (x y : V) :
      0 ≤ expectationJ G beta J (grahamPairSupport x y) :=
    pairCorrelation_nonneg G beta J hbeta hJ x y
  have hite (p : Prop) [Decidable p] (a b c e : V) :
      0 ≤ if p then
        expectationJ G beta J (grahamPairSupport a b) *
          expectationJ G beta J (grahamPairSupport c e) else 0 := by
    split
    · exact mul_nonneg (hC a b) (hC c e)
    · rfl
  have h1 := hite (i = j) i k i l
  have h2 := hite (i = k) i j i l
  have h3 := hite (i = l) i j i k
  have h4 := hite (j = k) j i j l
  have h5 := hite (j = l) j i j k
  have h6 := hite (k = l) k i k j
  by_cases hij : i = j
  · subst j
    rw [finiteCollisionFourthWeight, if_neg (by simp)]
    rw [finiteParityFourthUrsell_eq_of_firstPair]
    constructor
    · have hp := mul_nonneg (hC i k) (hC i l)
      nlinarith
    · unfold finiteCollisionFourthMajorant
      simp only [ite_true]
      nlinarith
  by_cases hik : i = k
  · subst k
    rw [finiteCollisionFourthWeight, if_neg (by simp)]
    rw [finiteParityFourthUrsell_eq_of_firstThird]
    constructor
    · have hp := mul_nonneg (hC i j) (hC i l)
      nlinarith
    · unfold finiteCollisionFourthMajorant
      simp only [ite_true]
      nlinarith
  by_cases hil : i = l
  · subst l
    rw [finiteCollisionFourthWeight, if_neg (by simp)]
    rw [finiteParityFourthUrsell_eq_of_firstFourth]
    constructor
    · have hp := mul_nonneg (hC i j) (hC i k)
      nlinarith
    · unfold finiteCollisionFourthMajorant
      simp only [ite_true]
      nlinarith
  by_cases hjk : j = k
  · subst k
    rw [finiteCollisionFourthWeight, if_neg (by simp)]
    rw [finiteParityFourthUrsell_eq_of_secondPair]
    constructor
    · have hp := mul_nonneg (hC j i) (hC j l)
      nlinarith
    · unfold finiteCollisionFourthMajorant
      simp only [ite_true]
      nlinarith
  by_cases hjl : j = l
  · subst l
    rw [finiteCollisionFourthWeight, if_neg (by simp)]
    rw [finiteParityFourthUrsell_eq_of_secondFourth]
    constructor
    · have hp := mul_nonneg (hC j i) (hC j k)
      nlinarith
    · unfold finiteCollisionFourthMajorant
      simp only [ite_true]
      nlinarith
  by_cases hkl : k = l
  · subst l
    rw [finiteCollisionFourthWeight, if_neg (by simp)]
    rw [finiteParityFourthUrsell_eq_of_thirdPair]
    constructor
    · have hp := mul_nonneg (hC k i) (hC k j)
      nlinarith
    · unfold finiteCollisionFourthMajorant
      simp only [ite_true]
      nlinarith
  · rw [finiteCollisionFourthWeight, if_pos]
    · constructor
      · rfl
      · unfold finiteCollisionFourthMajorant
        simp [hij, hik, hil, hjk, hjl, hkl]
    · exact ⟨hij, hik, hil, hjk, hjl, hkl⟩


end
end StatMech.FrontierA
