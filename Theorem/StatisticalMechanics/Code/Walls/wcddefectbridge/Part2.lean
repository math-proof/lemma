/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcddefectbridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.wadangledefect.Part4
import Theorem.StatisticalMechanics.Code.Walls.jc5_singlecycle.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Theorem.StatisticalMechanics.Code.Lattice.BalanceContraction.Part2
import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnet.Part4
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Def.StatisticalMechanics.Code.Walls.wcddefectbridge.Part2
open scoped BigOperators
open Finset
open SimpleGraph Function


namespace StatMech

namespace Wcd

open StatMech.Lattice

open StatMech.Wad

open StatMech.Euc


theorem wcd_mem_toVtxFinset (K : Set (Site 2)) (hK : K.Finite) (p : ℤ × ℤ) :
    p ∈ wcd_toVtxFinset K hK ↔ wcd_siteToVtx.symm p ∈ K := by
  classical
  unfold wcd_toVtxFinset
  rw [Finset.mem_image]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [Set.Finite.mem_toFinset] at hs
    rwa [Equiv.symm_apply_apply]
  · intro h
    exact ⟨wcd_siteToVtx.symm p, by rw [Set.Finite.mem_toFinset]; exact h, by simp⟩


theorem wcd_siteToVtx_mem_toVtxFinset (K : Set (Site 2)) (hK : K.Finite) (s : Site 2) :
    wcd_siteToVtx s ∈ wcd_toVtxFinset K hK ↔ s ∈ K := by
  rw [wcd_mem_toVtxFinset, Equiv.symm_apply_apply]


end Wcd
end StatMech
