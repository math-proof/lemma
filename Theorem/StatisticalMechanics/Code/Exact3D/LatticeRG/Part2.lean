/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LatticeRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Exact3D.RG.Part2
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Exact3D.LatticeRG.Part2


namespace StatMech

namespace Exact3D

open StatMech.Lattice


@[simp] theorem blockRemainder_apply {d : ℕ} (scale : BlockScale)
    (x : Site d) (i : Fin d) :
    blockRemainder scale x i = x i % (scale.L : ℤ) :=
  rfl

theorem blockRepresentative_blockIndexOf_add_blockRemainder {d : ℕ}
    (scale : BlockScale) (x : Site d) :
    blockRepresentative scale (blockIndexOf scale x) +
        blockRemainder scale x = x := by
  ext i
  simpa [blockRepresentative, blockIndexOf, blockRemainder] using
    Int.mul_ediv_add_emod (x i) (scale.L : ℤ)

theorem blockRemainder_nonneg {d : ℕ}
    (scale : BlockScale) (x : Site d) (i : Fin d) :
    0 ≤ blockRemainder scale x i := by
  simpa [blockRemainder] using
    Int.emod_nonneg (x i) (Int.ofNat_ne_zero.mpr scale.L_ne_zero)

theorem blockRemainder_lt_scale {d : ℕ}
    (scale : BlockScale) (x : Site d) (i : Fin d) :
    blockRemainder scale x i < (scale.L : ℤ) := by
  simpa [blockRemainder] using
    Int.emod_lt_of_pos (x i) (show 0 < (scale.L : ℤ) by
      exact_mod_cast lt_trans Nat.zero_lt_one scale.one_lt)

theorem blockRemainder_natAbs_lt_scale {d : ℕ}
    (scale : BlockScale) (x : Site d) (i : Fin d) :
    (blockRemainder scale x i).natAbs < scale.L := by
  have hcast :
      ((blockRemainder scale x i).natAbs : ℤ) < (scale.L : ℤ) := by
    rw [Int.natCast_natAbs,
      abs_of_nonneg (blockRemainder_nonneg scale x i)]
    exact blockRemainder_lt_scale scale x i
  exact_mod_cast hcast

@[simp] theorem blockRemainder_zero {d : ℕ} (scale : BlockScale) :
    blockRemainder scale (0 : Site d) = (0 : Site d) := by
  ext i
  simp [blockRemainder]

@[simp] theorem blockRemainder_blockRepresentative {d : ℕ}
    (scale : BlockScale) (b : BlockIndex d) :
    blockRemainder scale (blockRepresentative scale b) = (0 : Site d) := by
  ext i
  simp [blockRemainder, blockRepresentative, Int.mul_emod_right]


theorem blockRemainder_eq_zero_iff_exists_blockRepresentative {d : ℕ}
    (scale : BlockScale) (x : Site d) :
    blockRemainder scale x = 0 ↔
      ∃ b : BlockIndex d, blockRepresentative scale b = x := by
  constructor
  · intro hzero
    refine ⟨blockIndexOf scale x, ?_⟩
    have hdecomp :=
      blockRepresentative_blockIndexOf_add_blockRemainder scale x
    simpa [hzero] using hdecomp
  · rintro ⟨b, rfl⟩
    exact blockRemainder_blockRepresentative scale b

theorem blockIndexOf_blockRepresentative_add_of_remainder_bounds {d : ℕ}
    (scale : BlockScale) (b : BlockIndex d) (r : Site d)
    (hr_nonneg : ∀ i : Fin d, 0 ≤ r i)
    (hr_lt : ∀ i : Fin d, r i < (scale.L : ℤ)) :
    blockIndexOf scale (blockRepresentative scale b + r) = b := by
  ext i
  have hLne : (scale.L : ℤ) ≠ 0 :=
    Int.ofNat_ne_zero.mpr scale.L_ne_zero
  have hdiv : r i / (scale.L : ℤ) = 0 :=
    Int.ediv_eq_zero_of_lt (hr_nonneg i) (hr_lt i)
  calc
    blockIndexOf scale (blockRepresentative scale b + r) i =
        ((scale.L : ℤ) * b i + r i) / (scale.L : ℤ) := rfl
    _ = (r i + (scale.L : ℤ) * b i) / (scale.L : ℤ) := by
      rw [add_comm]
    _ = r i / (scale.L : ℤ) + b i := by
      exact Int.add_mul_ediv_left (r i) (b i) hLne
    _ = b i := by
      simp [hdiv]

theorem blockRemainder_blockRepresentative_add_of_remainder_bounds {d : ℕ}
    (scale : BlockScale) (b : BlockIndex d) (r : Site d)
    (hr_nonneg : ∀ i : Fin d, 0 ≤ r i)
    (hr_lt : ∀ i : Fin d, r i < (scale.L : ℤ)) :
    blockRemainder scale (blockRepresentative scale b + r) = r := by
  ext i
  calc
    blockRemainder scale (blockRepresentative scale b + r) i =
        ((scale.L : ℤ) * b i + r i) % (scale.L : ℤ) := rfl
    _ = (r i + (scale.L : ℤ) * b i) % (scale.L : ℤ) := by
      rw [add_comm]
    _ = r i % (scale.L : ℤ) := by
      exact Int.add_mul_emod_self_left (r i) (scale.L : ℤ) (b i)
    _ = r i := Int.emod_eq_of_lt (hr_nonneg i) (hr_lt i)

theorem block_decomposition_unique {d : ℕ} (scale : BlockScale)
    {b c : BlockIndex d} {r s : Site d}
    (hr_nonneg : ∀ i : Fin d, 0 ≤ r i)
    (hr_lt : ∀ i : Fin d, r i < (scale.L : ℤ))
    (hs_nonneg : ∀ i : Fin d, 0 ≤ s i)
    (hs_lt : ∀ i : Fin d, s i < (scale.L : ℤ))
    (h :
      blockRepresentative scale b + r =
        blockRepresentative scale c + s) :
    b = c ∧ r = s := by
  have hb : b = c := by
    calc
      b = blockIndexOf scale (blockRepresentative scale b + r) :=
        (blockIndexOf_blockRepresentative_add_of_remainder_bounds
          scale b r hr_nonneg hr_lt).symm
      _ = blockIndexOf scale (blockRepresentative scale c + s) := by
        rw [h]
      _ = c :=
        blockIndexOf_blockRepresentative_add_of_remainder_bounds
          scale c s hs_nonneg hs_lt
  have hr : r = s := by
    calc
      r = blockRemainder scale (blockRepresentative scale b + r) :=
        (blockRemainder_blockRepresentative_add_of_remainder_bounds
          scale b r hr_nonneg hr_lt).symm
      _ = blockRemainder scale (blockRepresentative scale c + s) := by
        rw [h]
      _ = s :=
        blockRemainder_blockRepresentative_add_of_remainder_bounds
          scale c s hs_nonneg hs_lt
  exact ⟨hb, hr⟩


end Exact3D
end StatMech
