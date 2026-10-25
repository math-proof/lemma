/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedFourth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianCriticalNewman.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianConePolarization.Part4
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianWeightedFourth
open Filter Finset Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem finiteWeightedParityFourthCumulant_bounds
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : forall e, 0 <= J e)
    (a : V -> Real) (M : Real)
    (hM : 0 <= M) (ha0 : forall i, 0 <= a i)
    (haM : forall i, a i <= M) :
    0 <= -finiteWeightedParityFourthCumulant G beta J a ∧
      -finiteWeightedParityFourthCumulant G beta J a <=
        M ^ 4 *
          (-(∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V,
            finiteParityFourthUrsell G beta J i j k l)) := by
  have hterm (i j k l : V) :
      0 <= -(a i * a j * a k * a l *
          finiteParityFourthUrsell G beta J i j k l) ∧
        -(a i * a j * a k * a l *
            finiteParityFourthUrsell G beta J i j k l) <=
          M ^ 4 * (-finiteParityFourthUrsell G beta J i j k l) := by
    have hU : 0 <= -finiteParityFourthUrsell G beta J i j k l :=
      neg_nonneg.mpr (finiteParityFourthUrsell_nonpos
        G beta J hbeta hJ i j k l)
    have haProd : 0 <= a i * a j * a k * a l :=
      mul_nonneg (mul_nonneg (mul_nonneg (ha0 i) (ha0 j)) (ha0 k)) (ha0 l)
    have haProdLe : a i * a j * a k * a l <= M ^ 4 := by
      have hij : a i * a j <= M * M :=
        mul_le_mul (haM i) (haM j) (ha0 j) hM
      have hkl : a k * a l <= M * M :=
        mul_le_mul (haM k) (haM l) (ha0 l) hM
      calc
        a i * a j * a k * a l = (a i * a j) * (a k * a l) := by ring
        _ <= (M * M) * (M * M) :=
          mul_le_mul hij hkl (mul_nonneg (ha0 k) (ha0 l))
            (mul_nonneg hM hM)
        _ = M ^ 4 := by ring
    constructor
    · nlinarith
    · nlinarith
  unfold finiteWeightedParityFourthCumulant
  have hweightedNeg :
      -(∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V,
          a i * a j * a k * a l *
            finiteParityFourthUrsell G beta J i j k l) =
        ∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V,
          -(a i * a j * a k * a l *
            finiteParityFourthUrsell G beta J i j k l) := by
    symm
    simp_rw [Finset.sum_neg_distrib]
  rw [hweightedNeg]
  constructor
  · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ =>
        (hterm i j k l).1
  · calc
      _ <= ∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V,
          M ^ 4 * (-finiteParityFourthUrsell G beta J i j k l) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ =>
            (hterm i j k l).2
      _ = M ^ 4 *
          (-(∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V,
            finiteParityFourthUrsell G beta J i j k l)) := by
        calc
          (∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V,
              M ^ 4 * (-finiteParityFourthUrsell G beta J i j k l)) =
              M ^ 4 * (∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V,
                -finiteParityFourthUrsell G beta J i j k l) := by
            simp_rw [Finset.mul_sum]
        _ = _ := by simp_rw [Finset.sum_neg_distrib]


end
end StatMech.FrontierA
