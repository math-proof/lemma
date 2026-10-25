/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredMomentumShell.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingInfraredContinuumGreen.Part2
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.FrontierA.IsingInfraredMomentumShell.Part2
open Finset Set
open scoped BigOperators


namespace StatMech.FrontierA

open Lattice


theorem integerMomentumBoxWithoutZero_succ (d M : Nat) :
    integerMomentumBoxWithoutZero d (M + 1) =
      integerMomentumBoxWithoutZero d M ∪ boxSV_vbF d (M + 1) := by
  classical
  ext m
  simp only [integerMomentumBoxWithoutZero, Finset.mem_sdiff,
    Finset.mem_singleton, Finset.mem_union, boxSV_vbF]
  constructor
  · rintro ⟨hmOuter, hm0⟩
    by_cases hmInner : m ∈ boxSV_boxF d M
    · exact Or.inl ⟨hmInner, hm0⟩
    · exact Or.inr ⟨by simpa only [Nat.add_sub_cancel] using hmOuter,
        by simpa only [Nat.add_sub_cancel] using hmInner⟩
  · rintro (⟨hmInner, hm0⟩ | ⟨hmOuter, hmNotInner⟩)
    · refine ⟨boxSV_boxF_subset d (Nat.le_succ M) hmInner, hm0⟩
    · refine ⟨hmOuter, ?_⟩
      intro hm0
      subst m
      apply hmNotInner
      rw [boxSV_mem_boxF]
      intro i
      simp

theorem disjoint_integerMomentumBoxWithoutZero_shell_succ (d M : Nat) :
    Disjoint (integerMomentumBoxWithoutZero d M) (boxSV_vbF d (M + 1)) := by
  classical
  rw [Finset.disjoint_left]
  intro m hmBox hmShell
  rw [integerMomentumBoxWithoutZero, Finset.mem_sdiff] at hmBox
  rw [boxSV_vbF, Finset.mem_sdiff] at hmShell
  exact hmShell.2 (by simpa only [Nat.add_sub_cancel] using hmBox.1)


theorem sum_inv_integerMomentumNormSq_box_eq_sum_shells (d M : Nat) :
    ∑ m ∈ integerMomentumBoxWithoutZero d M,
        (integerMomentumNormSq m)⁻¹ =
      ∑ r ∈ Finset.range M,
        ∑ m ∈ boxSV_vbF d (r + 1),
          (integerMomentumNormSq m)⁻¹ := by
  induction M with
  | zero =>
      have hzero : integerMomentumBoxWithoutZero d 0 = ∅ := by
        classical
        ext m
        simp only [integerMomentumBoxWithoutZero, Finset.mem_sdiff,
          Finset.mem_singleton, Finset.notMem_empty, iff_false]
        intro hm
        apply hm.2
        funext i
        have hi := (boxSV_mem_boxF.mp hm.1) i
        simp only [Finset.mem_Icc] at hi
        change m i = 0
        omega
      simp [hzero]
  | succ M ih =>
      rw [integerMomentumBoxWithoutZero_succ,
        Finset.sum_union (disjoint_integerMomentumBoxWithoutZero_shell_succ d M),
        ih, Finset.sum_range_succ]


theorem sum_inv_integerMomentumNormSq_box_le_power
    (d M : Nat) (hd : 3 ≤ d) :
    ∑ m ∈ integerMomentumBoxWithoutZero d M,
        (integerMomentumNormSq m)⁻¹ ≤
      2 * d * 3 ^ (d - 1) * (M : Real) ^ (d - 2) := by
  rw [sum_inv_integerMomentumNormSq_box_eq_sum_shells]
  by_cases hM : M = 0
  · subst M
    simp only [Finset.range_zero, Finset.sum_empty]
    positivity
  have hMpos : 0 < M := Nat.pos_of_ne_zero hM
  have hterm (r : Nat) (hr : r ∈ Finset.range M) :
      ∑ m ∈ boxSV_vbF d (r + 1),
          (integerMomentumNormSq m)⁻¹ ≤
        2 * d * 3 ^ (d - 1) * (M : Real) ^ (d - 3) := by
    calc
      ∑ m ∈ boxSV_vbF d (r + 1),
          (integerMomentumNormSq m)⁻¹ ≤
          2 * d * 3 ^ (d - 1) * ((r + 1 : Nat) : Real) ^ (d - 3) :=
        sum_inv_integerMomentumNormSq_shell_le_power d (r + 1) hd (by omega)
      _ ≤ 2 * d * 3 ^ (d - 1) * (M : Real) ^ (d - 3) := by
        gcongr
        exact_mod_cast (Finset.mem_range.mp hr)
  calc
    ∑ r ∈ Finset.range M,
        ∑ m ∈ boxSV_vbF d (r + 1),
          (integerMomentumNormSq m)⁻¹ ≤
        ∑ _r ∈ Finset.range M,
          2 * d * 3 ^ (d - 1) * (M : Real) ^ (d - 3) := by
      exact Finset.sum_le_sum hterm
    _ = 2 * d * 3 ^ (d - 1) * (M : Real) ^ (d - 2) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      calc
        (M : Real) *
            (2 * d * 3 ^ (d - 1) * (M : Real) ^ (d - 3)) =
            2 * d * 3 ^ (d - 1) *
              ((M : Real) * (M : Real) ^ (d - 3)) := by ring
        _ = 2 * d * 3 ^ (d - 1) * (M : Real) ^ (d - 2) := by
          rw [← pow_succ']
          congr 3
          omega

end StatMech.FrontierA
