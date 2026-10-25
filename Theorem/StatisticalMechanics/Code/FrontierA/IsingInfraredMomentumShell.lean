/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredMomentumShell.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingInfraredContinuumGreen.Part2
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.FrontierA.IsingInfraredMomentumShell
open Finset Set
open scoped BigOperators


namespace StatMech.FrontierA

open Lattice


theorem integerMomentumNormSq_nonneg {d : Nat} (m : Site d) :
    0 ≤ integerMomentumNormSq m := by
  unfold integerMomentumNormSq
  positivity

theorem integerMomentumNormSq_pos {d : Nat} {m : Site d} (hm : m ≠ 0) :
    0 < integerMomentumNormSq m := by
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra h
    apply hm
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  unfold integerMomentumNormSq
  exact Finset.sum_pos' (fun j _ ↦ sq_nonneg (m j : Real))
    ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero (by exact_mod_cast hi)⟩


theorem natCast_sq_le_integerMomentumNormSq_of_mem_shell
    {d r : Nat} {m : Site d} (hr : 1 ≤ r) (hm : m ∈ boxSV_vbF d r) :
    (r : Real) ^ 2 ≤ integerMomentumNormSq m := by
  have hm' : m ∈ vertexBoundary d r := by
    rw [← boxSV_coe_vbF d r]
    exact hm
  rw [mem_vertexBoundary] at hm'
  rw [mem_box] at hm'
  obtain ⟨i, hiInner⟩ := not_forall.mp hm'.2
  have hiOuter := hm'.1 i
  have hi : (m i).natAbs = r := by omega
  have hiSq : (r : Real) ^ 2 = (m i : Real) ^ 2 := by
    have hiReal : |(m i : Real)| = (r : Real) := by
      calc
        |(m i : Real)| = ((|m i| : Int) : Real) := Int.cast_abs.symm
        _ = (((m i).natAbs : Int) : Real) := by
          rw [Int.natCast_natAbs]
        _ = (r : Real) := by norm_cast
    nlinarith [sq_abs (m i : Real)]
  rw [hiSq, integerMomentumNormSq]
  exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (m j : Real))
    (Finset.mem_univ i)


theorem sum_inv_integerMomentumNormSq_shell_le
    (d r : Nat) (hr : 1 ≤ r) :
    ∑ m ∈ boxSV_vbF d r, (integerMomentumNormSq m)⁻¹ ≤
      ((boxSV_vbF d r).card : Real) / (r : Real) ^ 2 := by
  have hrPos : (0 : Real) < (r : Real) := by exact_mod_cast (Nat.zero_lt_of_lt hr)
  calc
    ∑ m ∈ boxSV_vbF d r, (integerMomentumNormSq m)⁻¹ ≤
        ∑ _m ∈ boxSV_vbF d r, ((r : Real) ^ 2)⁻¹ := by
      apply Finset.sum_le_sum
      intro m hm
      exact inv_anti₀ (sq_pos_of_pos hrPos)
        (natCast_sq_le_integerMomentumNormSq_of_mem_shell hr hm)
    _ = ((boxSV_vbF d r).card : Real) / (r : Real) ^ 2 := by
      simp [div_eq_mul_inv]

theorem integerMomentumShell_card_le (d r : Nat) (hr : 1 ≤ r) :
    ((boxSV_vbF d r).card : Real) ≤
      2 * d * (2 * (r : Real) + 1) ^ (d - 1) := by
  have hcard : (boxSV_vbF d r).card = boxSV_boundaryCard d r := by
    rw [boxSV_vbF_eq_toFinset]
    rfl
  rw [hcard, boxSV_boundary_card d r hr]
  have hle : (2 * r - 1) ^ d ≤ (2 * r + 1) ^ d :=
    Nat.pow_le_pow_left (by omega) d
  rw [Nat.cast_sub hle]
  have hrR : (1 : Real) ≤ r := by exact_mod_cast hr
  have hpow := boxSV_pow_sub_pow_le
    (2 * (r : Real) + 1) (2 * (r : Real) - 1)
    (by linarith) (by linarith) d
  have hminus : ((2 * r - 1 : Nat) : Real) = 2 * (r : Real) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * r)]
    push_cast
    ring
  push_cast
  rw [hminus]
  calc
    (2 * (r : Real) + 1) ^ d - (2 * (r : Real) - 1) ^ d ≤
        ((2 * (r : Real) + 1) - (2 * (r : Real) - 1)) *
          (d * (2 * (r : Real) + 1) ^ (d - 1)) := hpow
    _ = 2 * d * (2 * (r : Real) + 1) ^ (d - 1) := by ring


theorem sum_inv_integerMomentumNormSq_shell_le_power
    (d r : Nat) (hd : 3 ≤ d) (hr : 1 ≤ r) :
    ∑ m ∈ boxSV_vbF d r, (integerMomentumNormSq m)⁻¹ ≤
      2 * d * 3 ^ (d - 1) * (r : Real) ^ (d - 3) := by
  have hrPos : (0 : Real) < (r : Real) := by exact_mod_cast (Nat.zero_lt_of_lt hr)
  have hcard := integerMomentumShell_card_le d r hr
  have hthree : 2 * (r : Real) + 1 ≤ 3 * r := by
    have : (1 : Real) ≤ r := by exact_mod_cast hr
    linarith
  have hpow : (2 * (r : Real) + 1) ^ (d - 1) ≤
      (3 * (r : Real)) ^ (d - 1) := by
    exact pow_le_pow_left₀ (by positivity) hthree _
  calc
    ∑ m ∈ boxSV_vbF d r, (integerMomentumNormSq m)⁻¹ ≤
        ((boxSV_vbF d r).card : Real) / (r : Real) ^ 2 :=
      sum_inv_integerMomentumNormSq_shell_le d r hr
    _ ≤ (2 * d * (2 * (r : Real) + 1) ^ (d - 1)) /
        (r : Real) ^ 2 := by
      exact div_le_div_of_nonneg_right hcard (sq_nonneg (r : Real))
    _ ≤ (2 * d * (3 * (r : Real)) ^ (d - 1)) /
        (r : Real) ^ 2 := by
      gcongr
    _ = 2 * d * 3 ^ (d - 1) * (r : Real) ^ (d - 3) := by
      rw [mul_pow]
      field_simp
      ring_nf
      rw [← pow_add]
      congr 2
      omega


end StatMech.FrontierA
