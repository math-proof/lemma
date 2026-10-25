/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossingCover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossingCounterexample
import Theorem.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part13
import Theorem.StatisticalMechanics.Code.Universality.BXPAllAspect
import Def.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossingCover.Part3
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.Onsager

open StatMech.RSW.Box

open StatMech.Universality


theorem torusReduceSite_val_of_mem_rect (L n : ℕ) (hnL : n < L)
    {x : Site 2} (hx : x ∈ rect 0 (n : ℤ) 0 (n : ℤ)) :
    (torusReduceSite L x).1.val = Int.toNat (x 0) ∧
      (torusReduceSite L x).2.val = Int.toNat (x 1) := by
  rw [mem_rect] at hx
  letI : NeZero L := ⟨by omega⟩
  have hL : (0 : ℤ) < L := by omega
  constructor
  · change (x 0 : ZMod L).val = Int.toNat (x 0)
    have hxL : x 0 < L := by omega
    apply Nat.cast_injective (R := ℤ)
    calc
      ((x 0 : ZMod L).val : ℤ) = x 0 % (L : ℤ) := ZMod.val_intCast (x 0)
      _ = x 0 := Int.emod_eq_of_lt hx.1 hxL
      _ = (Int.toNat (x 0) : ℤ) := (Int.toNat_of_nonneg hx.1).symm
  · change (x 1 : ZMod L).val = Int.toNat (x 1)
    have hxL : x 1 < L := by omega
    apply Nat.cast_injective (R := ℤ)
    calc
      ((x 1 : ZMod L).val : ℤ) = x 1 % (L : ℤ) := ZMod.val_intCast (x 1)
      _ = x 1 := Int.emod_eq_of_lt hx.2.2.1 hxL
      _ = (Int.toNat (x 1) : ℤ) := (Int.toNat_of_nonneg hx.2.2.1).symm

theorem torusReduceSite_mem_square (L n : ℕ) (hnL : n < L)
    {x : Site 2} (hx : x ∈ rect 0 (n : ℤ) 0 (n : ℤ)) :
    torusReduceSite L x ∈ torusSquareVertexSet L n := by
  obtain ⟨h0, h1⟩ := torusReduceSite_val_of_mem_rect L n hnL hx
  change (torusReduceSite L x).1.val ≤ n ∧
    (torusReduceSite L x).2.val ≤ n
  rw [h0, h1]
  rw [mem_rect] at hx
  omega


end StatMech.BeffaraDC
