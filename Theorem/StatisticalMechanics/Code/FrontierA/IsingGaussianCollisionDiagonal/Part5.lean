/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCollisionDiagonal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianCriticalSummation.Part5
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianCollisionDiagonal.Part5
open Filter Finset Set Topology
open scoped BigOperators symmDiff


namespace StatMech.FrontierA

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


section CriticalFiniteBox

theorem criticalFiniteBoxFullRenormalizedFourthCoupling_bounds
    (hd : 2 ≤ d) (n : Nat) :
    0 ≤ criticalFiniteBoxFullRenormalizedFourthCoupling d n ∧
      criticalFiniteBoxFullRenormalizedFourthCoupling d n ≤
        criticalFreeBoxSusceptibility d (2 * n) ^ 2 /
            ((2 * n + 1 : Nat) : Real) ^ d +
          6 / ((2 * n + 1 : Nat) : Real) ^ d := by
  let U : Real := -criticalFiniteBoxParityIntegratedFourthCumulant d n
  let chi : Real := criticalFreeBoxSusceptibility d (2 * n)
  let radius : Real := ((2 * n + 1 : Nat) : Real)
  have hbeta : 0 ≤ IsingFK.betaC (magnetization d) := by
    rw [isingFK_betaC_eq_tildeBetaCIsing hd]
    exact (tildeBetaCIsing_pos hd).le
  have hU : 0 ≤ U ∧ U ≤ 2 * chi ^ 4 + 12 * chi ^ 2 := by
    simpa [U, chi, criticalFiniteBoxParityIntegratedFourthCumulant] using
      finiteParityIntegratedFourthCumulant_treeDiagram_bound
        (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (fun _ => 1)
        hbeta (fun _ => by norm_num) chi
        (criticalFreeBoxSusceptibility_nonneg hd (2 * n))
        (criticalFiniteBoxRowSusceptibility_le hd n)
        (criticalFiniteBoxOrigin d n)
  have hchi : 0 < chi := by
    have := one_le_criticalFreeBoxSusceptibility hd (2 * n)
    dsimp [chi]
    linarith
  have hradius : 0 < radius := by
    dsimp [radius]
    positivity
  have hden : 0 < 2 * chi ^ 2 * radius ^ d := by positivity
  change 0 ≤ U / (2 * chi ^ 2 * radius ^ d) ∧
    U / (2 * chi ^ 2 * radius ^ d) ≤
      chi ^ 2 / radius ^ d + 6 / radius ^ d
  constructor
  · exact div_nonneg hU.1 hden.le
  · rw [div_le_iff₀ hden]
    calc
      U ≤ 2 * chi ^ 4 + 12 * chi ^ 2 := hU.2
      _ = (chi ^ 2 / radius ^ d + 6 / radius ^ d) *
          (2 * chi ^ 2 * radius ^ d) := by
        field_simp [ne_of_gt hradius]
        ring


theorem criticalFiniteBoxFullRenormalizedFourthCoupling_tendsto_zero
    (d : Nat) (hd : 4 < d) :
    Tendsto (fun n => criticalFiniteBoxFullRenormalizedFourthCoupling d n)
      atTop (nhds 0) := by
  obtain ⟨A, hA, hchiUpper⟩ :=
    exists_criticalFreeBoxSusceptibility_le_quadratic (d := d) (by omega)
  let radius : Nat → Real := fun n => ((2 * n + 1 : Nat) : Real)
  let chi : Nat → Real := fun n => criticalFreeBoxSusceptibility d (2 * n)
  have hradiusNat : Tendsto (fun n : Nat => 2 * n + 1) atTop atTop := by
    rw [tendsto_atTop]
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    omega
  have hradius : Tendsto radius atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hradiusNat
  have hpower (p : Nat) (hp : 0 < p) :
      Tendsto (fun n => radius n ^ p) atTop atTop := by
    apply Filter.tendsto_atTop_mono (fun n => ?_) hradius
    have hradiusOne : 1 ≤ radius n := by
      dsimp [radius]
      norm_num
    simpa only [pow_one] using pow_le_pow_right₀ hradiusOne hp
  have hmain : Tendsto
      (fun n => A ^ 2 / radius n ^ (d - 4)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (hpower (d - 4) (by omega))
  have hcollision : Tendsto
      (fun n => 6 / radius n ^ d) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (hpower d (by omega))
  have henvelope : Tendsto
      (fun n => A ^ 2 / radius n ^ (d - 4) + 6 / radius n ^ d)
      atTop (nhds 0) := by
    simpa using hmain.add hcollision
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun n =>
      (criticalFiniteBoxFullRenormalizedFourthCoupling_bounds (d := d)
        (by omega) n).1) _ henvelope
  filter_upwards with n
  have hradiusPos : 0 < radius n := by
    dsimp [radius]
    positivity
  have hchiNonneg : 0 ≤ chi n := by
    dsimp [chi]
    exact criticalFreeBoxSusceptibility_nonneg (by omega) (2 * n)
  have hchiLe : chi n ≤ A * radius n ^ 2 := by
    simpa [chi, radius] using hchiUpper (2 * n)
  have hchiSq : chi n ^ 2 ≤ (A * radius n ^ 2) ^ 2 :=
    (sq_le_sq₀ hchiNonneg (by positivity)).2 hchiLe
  calc
    criticalFiniteBoxFullRenormalizedFourthCoupling d n ≤
        chi n ^ 2 / radius n ^ d + 6 / radius n ^ d := by
      simpa [chi, radius] using
        (criticalFiniteBoxFullRenormalizedFourthCoupling_bounds (d := d)
          (by omega) n).2
    _ ≤ (A * radius n ^ 2) ^ 2 / radius n ^ d +
          6 / radius n ^ d := by
      gcongr
    _ = A ^ 2 / radius n ^ (d - 4) + 6 / radius n ^ d := by
      congr 1
      have hd' : d = (d - 4) + 4 := by omega
      rw [hd', pow_add]
      field_simp
      congr 3
      omega

end CriticalFiniteBox
end
end StatMech.FrontierA
