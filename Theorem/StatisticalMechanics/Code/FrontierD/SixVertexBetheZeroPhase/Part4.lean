/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeRoots.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCoordinateBetheOne.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhase.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexZeroPhaseBethePrefactor_eq
    {n : Nat} {c : Real} (hc : 2 < c) (N : Nat)
    (p : Fin n -> Real) (ell : Fin n) (hell : p ell = 0) :
    sixVertexZeroPhaseBethePrefactor c N p ell =
      c ^ 2 * ((N : Real) +
        ∑ j, sixVertexThetaLeftDerivAtZero c (p j)) := by
  have hc0 : c ≠ 0 := by linarith
  have hsplit :
      (∑ j, sixVertexThetaLeftDerivAtZero c (p j)) =
        sixVertexThetaLeftDerivAtZero c (p ell) +
          ∑ j ∈ (Finset.univ.erase ell),
            sixVertexThetaLeftDerivAtZero c (p j) := by
    have herase := Finset.sum_erase_add Finset.univ
      (fun j => sixVertexThetaLeftDerivAtZero c (p j))
      (Finset.mem_univ ell)
    rw [← herase]
    ring
  rw [hsplit, hell, sixVertexThetaLeftDerivAtZero_self hc]
  unfold sixVertexZeroPhaseBethePrefactor
  field_simp [hc0]
  ring

theorem sixVertexZeroPhaseBethePrefactor_pos
    {n N : Nat} {c : Real} (hc : 2 < c) (hhalf : 2 * n <= N)
    (p : Fin n -> Real) (ell : Fin n) (hell : p ell = 0) :
    0 < sixVertexZeroPhaseBethePrefactor c N p ell := by
  have hnonempty : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨ell, Finset.mem_univ ell⟩
  have hsum : ∑ _j : Fin n, (-2 : Real) <
      ∑ j : Fin n, sixVertexThetaLeftDerivAtZero c (p j) := by
    apply Finset.sum_lt_sum
    · intro j hj
      exact (neg_two_lt_sixVertexThetaLeftDerivAtZero hc (p j)).le
    · obtain ⟨j, hj⟩ := hnonempty
      exact ⟨j, hj, neg_two_lt_sixVertexThetaLeftDerivAtZero hc (p j)⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsum
  rw [sixVertexZeroPhaseBethePrefactor_eq hc N p ell hell]
  have hn : (2 : Real) * n <= N := by exact_mod_cast hhalf
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos (by linarith)
  apply mul_pos hc2
  linarith

theorem sixVertexThetaLeftDerivAtZero_neg
    {c : Real} (hc : 2 < c) (y : Real) :
    sixVertexThetaLeftDerivAtZero c y < 0 := by
  exact sixVertexTheta_left_deriv_neg hc 0 y

theorem sixVertexZeroPhaseBethePrefactor_bounds
    {n N : Nat} {c : Real} (hc : 2 < c)
    (p : Fin n -> Real) (ell : Fin n) (hell : p ell = 0) :
    c ^ 2 * ((N : Real) - 2 * (n : Real)) <
        sixVertexZeroPhaseBethePrefactor c N p ell ∧
      sixVertexZeroPhaseBethePrefactor c N p ell <= c ^ 2 * (N : Real) := by
  have hnonempty : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨ell, Finset.mem_univ ell⟩
  have hlower : ∑ _j : Fin n, (-2 : Real) <
      ∑ j : Fin n, sixVertexThetaLeftDerivAtZero c (p j) := by
    apply Finset.sum_lt_sum
    · intro j hj
      exact (neg_two_lt_sixVertexThetaLeftDerivAtZero hc (p j)).le
    · obtain ⟨j, hj⟩ := hnonempty
      exact ⟨j, hj, neg_two_lt_sixVertexThetaLeftDerivAtZero hc (p j)⟩
  have hupper :
      ∑ j : Fin n, sixVertexThetaLeftDerivAtZero c (p j) <= 0 := by
    exact Finset.sum_nonpos fun j hj =>
      (sixVertexThetaLeftDerivAtZero_neg hc (p j)).le
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hlower
  rw [sixVertexZeroPhaseBethePrefactor_eq hc N p ell hell]
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos (by linarith)
  constructor
  · exact mul_lt_mul_of_pos_left (by linarith) hc2
  · exact mul_le_mul_of_nonneg_left (by linarith) hc2.le


end
end StatMech.FrontierD
