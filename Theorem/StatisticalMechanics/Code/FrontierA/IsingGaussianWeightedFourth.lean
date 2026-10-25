/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedFourth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianCriticalNewman.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianConePolarization.Part4
open Filter Finset Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem finiteParityFourthUrsell_eq_finiteIsing_distinct
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) {i j k l : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    finiteParityFourthUrsell G beta J i j k l =
      finiteIsingFourthUrsell G beta J i j k l := by
  have hpair (x y : V) (hxy : x ≠ y) :
      grahamPairSupport x y = {x, y} := by
    ext z
    simp only [grahamPairSupport, Finset.mem_symmDiff,
      Finset.mem_singleton, Finset.mem_insert]
    aesop
  have hquad : grahamFourSupport i j k l = {i, j, k, l} := by
    rw [grahamFourSupport, hpair i j hij, hpair k l hkl]
    ext z
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    aesop
  unfold finiteParityFourthUrsell finiteIsingFourthUrsell
  rw [hquad, hpair i j hij, hpair i k hik, hpair i l hil,
    hpair j k hjk, hpair j l hjl, hpair k l hkl]


theorem finiteParityFourthUrsell_nonpos
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : forall e, 0 <= J e)
    (i j k l : V) :
    finiteParityFourthUrsell G beta J i j k l <= 0 := by
  by_cases h : i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l
  · rw [finiteParityFourthUrsell_eq_finiteIsing_distinct G beta J
      h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2,
      finiteIsingFourthUrsell_eq_current]
    exact finiteCurrentFourthUrsell_nonpos G beta J hbeta hJ
      h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
  · have hw :=
      (finiteCollisionFourthWeight_nonneg_le
        G beta J hbeta hJ i j k l).1
    rw [finiteCollisionFourthWeight, if_neg h] at hw
    linarith


end
end StatMech.FrontierA
