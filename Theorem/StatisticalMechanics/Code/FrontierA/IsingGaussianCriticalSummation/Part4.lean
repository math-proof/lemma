/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCriticalSummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalCubeInfrared
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianIndependentDisentangling.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianCriticalSummation.Part4
open Filter Finset Set Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB

noncomputable section

variable {d : Nat}


section CriticalFiniteBox

theorem criticalFiniteBoxRowSusceptibility_le
    (hd : 2 ≤ d) (n : Nat) (y : sctBox d n) :
    criticalFiniteBoxRowSusceptibility d n y ≤
      criticalFreeBoxSusceptibility d (2 * n) := by
  let shift : sctBox d n → Site d := fun x => y.1 - x.1
  have hshift : Function.Injective shift := by
    intro x z hxz
    apply Subtype.ext
    exact sub_right_inj.mp hxz
  have himage : Finset.univ.image shift ⊆ boxSV_boxF d (2 * n) := by
    intro w hw
    rw [Finset.mem_image] at hw
    obtain ⟨x, _hx, rfl⟩ := hw
    change y.1 - x.1 ∈ (boxSV_boxF d (2 * n) : Set (Site d))
    rw [boxSV_coe_boxF]
    exact sct_translate_box_subset_double x.2 ⟨y.1, y.2, rfl⟩
  calc
    criticalFiniteBoxRowSusceptibility d n y ≤
        ∑ x : sctBox d n,
          currentContinuityFreePairKernel d
            (IsingFK.betaC (magnetization d)) (shift x) := by
      unfold criticalFiniteBoxRowSusceptibility
      apply Finset.sum_le_sum
      intro x _hx
      exact criticalFiniteBoxPairCorrelation_le_infinite hd n x y
    _ = ∑ w ∈ Finset.univ.image shift,
          currentContinuityFreePairKernel d
            (IsingFK.betaC (magnetization d)) w := by
      rw [Finset.sum_image hshift.injOn]
    _ ≤ ∑ w ∈ boxSV_boxF d (2 * n),
          currentContinuityFreePairKernel d
            (IsingFK.betaC (magnetization d)) w := by
      exact Finset.sum_le_sum_of_subset_of_nonneg himage
        (fun w _hw _ => criticalFreePairKernel_nonneg hd w)
    _ = criticalFreeBoxSusceptibility d (2 * n) := by
      rw [criticalFreeBoxSusceptibility]


theorem criticalFiniteBoxDistinctIntegratedFourthCumulant_treeDiagram_bound
    (hd : 2 ≤ d) (n : Nat) (i : sctBox d n) :
    0 ≤ -finiteDistinctIntegratedFourthCumulant
        (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (fun _ => 1) i ∧
      -finiteDistinctIntegratedFourthCumulant
          (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (fun _ => 1) i ≤
        2 * criticalFreeBoxSusceptibility d (2 * n) ^ 4 := by
  have hbeta : 0 ≤ IsingFK.betaC (magnetization d) := by
    rw [isingFK_betaC_eq_tildeBetaCIsing hd]
    exact (tildeBetaCIsing_pos hd).le
  exact finiteDistinctIntegratedFourthCumulant_treeDiagram_bound
    (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (fun _ => 1)
    hbeta (fun _ => by norm_num) (criticalFreeBoxSusceptibility d (2 * n))
    (criticalFreeBoxSusceptibility_nonneg hd (2 * n))
    (criticalFiniteBoxRowSusceptibility_le hd n) i


end CriticalFiniteBox
end
end StatMech.FrontierA
