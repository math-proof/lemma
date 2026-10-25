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
import Def.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part3


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem ising3D_positiveMagnetizationSet_nonempty_of_meanfield
    (htc_pos : 0 < Sharpness.tildeBetaCIsing 3)
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β) :
    (Ising.positiveMagnetizationSet 3).Nonempty := by
  refine ⟨Sharpness.tildeBetaCIsing 3 + 1, ?_⟩
  rw [Ising.mem_positiveMagnetizationSet]
  exact
    Sharpness.posMag_of_meanfield_sqrt
      (d := 3) htc_pos hsqrt
      (Sharpness.tildeBetaCIsing 3 + 1) (by linarith)

set_option linter.style.longLine false in


theorem ising3D_positiveMagnetizationSet_bddBelow_of_vanish_below_tildeBetaC
    (hzero : ∀ β, β < Sharpness.tildeBetaCIsing 3 →
      Ising.magnetization 3 β = 0) :
    BddBelow (Ising.positiveMagnetizationSet 3) := by
  refine ⟨Sharpness.tildeBetaCIsing 3, ?_⟩
  intro β hβ
  rw [Ising.mem_positiveMagnetizationSet] at hβ
  by_contra hnot
  rw [not_le] at hnot
  have hz := hzero β hnot
  rw [hz] at hβ
  exact lt_irrefl 0 hβ

set_option linter.style.longLine false in


theorem ising3D_tildeBetaCIsing_pos_of_positive_mem
    (hbdd : BddAbove (Sharpness.tildeBetaCIsingSet 3))
    {β0 : ℝ}
    (hβ0 : 0 < β0)
    (hmem : β0 ∈ Sharpness.tildeBetaCIsingSet 3) :
    0 < Sharpness.tildeBetaCIsing 3 := by
  unfold Sharpness.tildeBetaCIsing
  exact lt_of_lt_of_le hβ0 (le_csSup hbdd hmem)

set_option linter.style.longLine false in


theorem ising3D_tildeBetaCIsing_pos_of_positive_phi_witness
    (hbdd : BddAbove (Sharpness.tildeBetaCIsingSet 3))
    {β0 : ℝ}
    (hβ0 : 0 < β0)
    (S : Finset (StatMech.Lattice.Site 3))
    (hS : StatMech.Percolation.origin 3 ∈ S)
    (hphi : Sharpness.phiIsing 3 β0 S < 1) :
    0 < Sharpness.tildeBetaCIsing 3 :=
  ising3D_tildeBetaCIsing_pos_of_positive_mem
    hbdd hβ0 ⟨le_of_lt hβ0, S, hS, hphi⟩

set_option linter.style.longLine false in


theorem corrOriginInner_le_one
    (d : ℕ) (β : ℝ) (S : Finset (StatMech.Lattice.Site d))
    (x : StatMech.Lattice.Site d) :
    Sharpness.corrOriginInner d β S x ≤ 1 := by
  classical
  unfold Sharpness.corrOriginInner
  split
  · split
    · exact le_trans (le_abs_self _) (Sharpness.abs_freeCorr_le_one d β S _ _)
    · norm_num
  · norm_num

set_option linter.style.longLine false in


theorem phiIsing_le_tanh_mul_boundaryEdges_card
    (d : ℕ) {β : ℝ} (hβ : 0 ≤ β)
    (S : Finset (StatMech.Lattice.Site d)) :
    Sharpness.phiIsing d β S ≤
      Real.tanh β * (StatMech.Percolation.boundaryEdges d S).card := by
  unfold Sharpness.phiIsing
  have htanh_nonneg : 0 ≤ Real.tanh β := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hβ) (Real.cosh_pos _).le
  apply mul_le_mul_of_nonneg_left _ htanh_nonneg
  calc
    ∑ e ∈ StatMech.Percolation.boundaryEdges d S,
        Sharpness.corrOriginInner d β S e.1
        ≤ ∑ _e ∈ StatMech.Percolation.boundaryEdges d S, (1 : ℝ) :=
          Finset.sum_le_sum (fun e _ => corrOriginInner_le_one d β S e.1)
    _ = (StatMech.Percolation.boundaryEdges d S).card := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]

set_option linter.style.longLine false in


theorem phiIsing_le_tanh_mul_card_mul_two_d
    (d : ℕ) {β : ℝ} (hβ : 0 ≤ β)
    (S : Finset (StatMech.Lattice.Site d)) :
    Sharpness.phiIsing d β S ≤ Real.tanh β * (S.card * (2 * d)) := by
  have hboundary :=
    phiIsing_le_tanh_mul_boundaryEdges_card d hβ S
  have htanh_nonneg : 0 ≤ Real.tanh β := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hβ) (Real.cosh_pos _).le
  have hcard :
      ((StatMech.Percolation.boundaryEdges d S).card : ℝ) ≤
        S.card * (2 * d) := by
    exact_mod_cast StatMech.Percolation.card_boundaryEdges_le_su
      (d := d) S
  exact le_trans hboundary (mul_le_mul_of_nonneg_left hcard htanh_nonneg)

set_option linter.style.longLine false in


theorem tildeBetaCIsingSet_mem_of_tanh_card_mul_two_d_lt_one
    {β : ℝ}
    (hβ : 0 ≤ β)
    (S : Finset (StatMech.Lattice.Site 3))
    (hS : StatMech.Percolation.origin 3 ∈ S)
    (hsmall : Real.tanh β * (S.card * (2 * 3)) < 1) :
    β ∈ Sharpness.tildeBetaCIsingSet 3 := by
  rw [Sharpness.mem_tildeBetaCIsingSet]
  refine ⟨hβ, S, hS, ?_⟩
  exact lt_of_le_of_lt
    (phiIsing_le_tanh_mul_card_mul_two_d 3 hβ S) hsmall

end Exact3D
end StatMech
