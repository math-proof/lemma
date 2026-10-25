/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part136
import Theorem.StatisticalMechanics.Code.Exact3D.BoundaryGhostHardField.Part7
import Theorem.StatisticalMechanics.Code.Exact3D.ExponentTheorem
import Theorem.StatisticalMechanics.Code.Exact3D.FKReparameterization.Part5
import Theorem.StatisticalMechanics.Code.Percolation.SharpnessUnconditional.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.BcEqIsing
import Theorem.StatisticalMechanics.Code.Ising.TransitionAssembly
import Def.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part4


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem ising3D_tildeBetaCIsingSet_positive_singleton_mem :
    ising3DPositiveWitnessBeta ∈ Sharpness.tildeBetaCIsingSet 3 := by
  classical
  have hβ_pos : 0 < ising3DPositiveWitnessBeta := by
    rw [ising3DPositiveWitnessBeta]
    exact Real.artanh_pos (by norm_num : (1 / 7 : ℝ) ∈ Set.Ioo 0 1)
  refine
    tildeBetaCIsingSet_mem_of_tanh_card_mul_two_d_lt_one
      (le_of_lt hβ_pos) ising3DOriginSingleton ?_ ?_
  · rw [ising3DOriginSingleton]
    exact Finset.mem_singleton_self _
  · have htanh :
        Real.tanh ising3DPositiveWitnessBeta = (1 / 7 : ℝ) := by
      rw [ising3DPositiveWitnessBeta]
      exact Real.tanh_artanh
        (by norm_num : (1 / 7 : ℝ) ∈ Set.Ioo (-1) 1)
    rw [htanh, ising3DOriginSingleton, Finset.card_singleton]
    norm_num

set_option linter.style.longLine false in


theorem ising3D_tildeBetaCIsing_pos_of_bddAbove
    (hbdd : BddAbove (Sharpness.tildeBetaCIsingSet 3)) :
    0 < Sharpness.tildeBetaCIsing 3 :=
  ising3D_tildeBetaCIsing_pos_of_positive_mem
    hbdd
    (by
      rw [ising3DPositiveWitnessBeta]
      exact Real.artanh_pos (by norm_num : (1 / 7 : ℝ) ∈ Set.Ioo 0 1))
    ising3D_tildeBetaCIsingSet_positive_singleton_mem

set_option linter.style.longLine false in


theorem tildeBetaCIsingSet_bddAbove_of_phi_barrier
    {B : ℝ}
    (hbarrier : ∀ β, B < β →
      ∀ S : Finset (StatMech.Lattice.Site 3),
        StatMech.Percolation.origin 3 ∈ S →
          1 ≤ Sharpness.phiIsing 3 β S) :
    BddAbove (Sharpness.tildeBetaCIsingSet 3) := by
  refine ⟨B, ?_⟩
  intro β hβ
  rw [Sharpness.mem_tildeBetaCIsingSet] at hβ
  obtain ⟨_, S, hS, hphi⟩ := hβ
  by_contra hnot
  rw [not_le] at hnot
  have hge := hbarrier β hnot S hS
  linarith

set_option linter.style.longLine false in


theorem ising3D_tildeBetaCIsing_pos_of_phi_barrier
    {B : ℝ}
    (hbarrier : ∀ β, B < β →
      ∀ S : Finset (StatMech.Lattice.Site 3),
        StatMech.Percolation.origin 3 ∈ S →
          1 ≤ Sharpness.phiIsing 3 β S) :
    0 < Sharpness.tildeBetaCIsing 3 :=
  ising3D_tildeBetaCIsing_pos_of_bddAbove
    (tildeBetaCIsingSet_bddAbove_of_phi_barrier hbarrier)

set_option linter.style.longLine false in


theorem tildeBetaCIsingSet_bddAbove_of_zero_on_set_and_eventual_pos
    (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 →
      Ising.magnetization 3 β = 0)
    (heventual : ∃ B : ℝ, ∀ β, B < β →
      0 < Ising.magnetization 3 β) :
    BddAbove (Sharpness.tildeBetaCIsingSet 3) := by
  obtain ⟨B, hpos⟩ := heventual
  refine ⟨B, ?_⟩
  intro β hβ
  by_contra hnot
  rw [not_le] at hnot
  have hz := hzeroSet β hβ
  have hp := hpos β hnot
  rw [hz] at hp
  exact lt_irrefl 0 hp

set_option linter.style.longLine false in


theorem ising3D_tildeBetaCIsing_pos_of_zero_on_set_and_eventual_pos
    (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 →
      Ising.magnetization 3 β = 0)
    (heventual : ∃ B : ℝ, ∀ β, B < β →
      0 < Ising.magnetization 3 β) :
    0 < Sharpness.tildeBetaCIsing 3 :=
  ising3D_tildeBetaCIsing_pos_of_bddAbove
    (tildeBetaCIsingSet_bddAbove_of_zero_on_set_and_eventual_pos
      hzeroSet heventual)

end Exact3D
end StatMech
