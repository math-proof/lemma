/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedFourth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianCriticalNewman.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianConePolarization.Part4
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianWeightedFourth.Part3
open Filter Finset Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

section CriticalBox

theorem criticalFiniteBoxWeightedParityFourthCumulant_bounds
    (d n : Nat) (hd : 2 <= d) (a : sctBox d n -> Real)
    (ha0 : forall i, 0 <= a i) (ha1 : forall i, a i <= 1) :
    0 <= -criticalFiniteBoxWeightedParityFourthCumulant d n a ∧
      -criticalFiniteBoxWeightedParityFourthCumulant d n a <=
        -criticalFiniteBoxGlobalParityFourthCumulant d n := by
  have hbeta : 0 <= IsingFK.betaC (magnetization d) := by
    rw [isingFK_betaC_eq_tildeBetaCIsing hd]
    exact (tildeBetaCIsing_pos hd).le
  have h := finiteWeightedParityFourthCumulant_bounds
    (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (fun _ => 1)
    hbeta (fun _ => by norm_num) a 1 (by norm_num) ha0 ha1
  simpa [criticalFiniteBoxWeightedParityFourthCumulant,
    criticalFiniteBoxGlobalParityFourthCumulant,
    finiteParityIntegratedFourthCumulant] using h

theorem criticalFiniteBoxWeightedNormalizedFourthCumulant_bounds
    (d n : Nat) (hd : 2 <= d) (a : sctBox d n -> Real)
    (ha0 : forall i, 0 <= a i) (ha1 : forall i, a i <= 1) :
    0 <= -criticalFiniteBoxWeightedNormalizedFourthCumulant d n a ∧
      -criticalFiniteBoxWeightedNormalizedFourthCumulant d n a <=
        -criticalFiniteBoxGlobalNormalizedFourthCumulant d n := by
  let denominator : Real :=
    2 * (Fintype.card (sctBox d n) : Real) *
      criticalFreeBoxSusceptibility d (2 * n) ^ 2 *
      ((2 * n + 1 : Nat) : Real) ^ d
  have hcard : 0 < (Fintype.card (sctBox d n) : Real) := by
    exact_mod_cast Fintype.card_pos_iff.mpr
      ⟨criticalFiniteBoxOrigin d n⟩
  have hchi : 0 < criticalFreeBoxSusceptibility d (2 * n) := by
    linarith [one_le_criticalFreeBoxSusceptibility hd (2 * n)]
  have hdenominator : 0 < denominator := by
    dsimp [denominator]
    positivity
  have hraw :=
    criticalFiniteBoxWeightedParityFourthCumulant_bounds d n hd a ha0 ha1
  have hweightedNormalized :
      -criticalFiniteBoxWeightedNormalizedFourthCumulant d n a =
        -criticalFiniteBoxWeightedParityFourthCumulant d n a / denominator := by
    dsimp [criticalFiniteBoxWeightedNormalizedFourthCumulant, denominator]
    ring
  have hglobalNormalized :
      -criticalFiniteBoxGlobalNormalizedFourthCumulant d n =
        -criticalFiniteBoxGlobalParityFourthCumulant d n / denominator := by
    dsimp [criticalFiniteBoxGlobalNormalizedFourthCumulant, denominator]
    ring
  rw [hweightedNormalized, hglobalNormalized]
  exact ⟨div_nonneg hraw.1 hdenominator.le,
    div_le_div_of_nonneg_right hraw.2 hdenominator.le⟩


theorem criticalFiniteBoxWeightedNormalizedFourthCumulant_tendsto_zero
    (d : Nat) (hd : 4 < d)
    (a : (n : Nat) -> sctBox d n -> Real)
    (ha0 : forall n i, 0 <= a n i)
    (ha1 : forall n i, a n i <= 1) :
    Tendsto
      (fun n => criticalFiniteBoxWeightedNormalizedFourthCumulant d n (a n))
      atTop (nhds 0) := by
  have hupper : Tendsto
      (fun n => -criticalFiniteBoxGlobalNormalizedFourthCumulant d n)
      atTop (nhds 0) :=
    by
      simpa only [neg_zero] using
        (criticalFiniteBoxGlobalNormalizedFourthCumulant_tendsto_zero d hd).neg
  have hneg : Tendsto
      (fun n => -criticalFiniteBoxWeightedNormalizedFourthCumulant d n (a n))
      atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun n =>
        (criticalFiniteBoxWeightedNormalizedFourthCumulant_bounds
          d n (by omega) (a n) (ha0 n) (ha1 n)).1
    · exact Filter.Eventually.of_forall fun n =>
        (criticalFiniteBoxWeightedNormalizedFourthCumulant_bounds
          d n (by omega) (a n) (ha0 n) (ha1 n)).2
    · exact hupper
  simpa using hneg.neg

end CriticalBox
end
end StatMech.FrontierA
