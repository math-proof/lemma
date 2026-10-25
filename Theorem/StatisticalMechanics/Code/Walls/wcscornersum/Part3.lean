/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcscornersum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.wadangledefect.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnet.Part4
import Theorem.StatisticalMechanics.Code.Walls.jc5_singlecycle.Part2
import Def.StatisticalMechanics.Code.Walls.wcscornersum.Part3
open scoped BigOperators
open Finset
open SimpleGraph Function


namespace StatMech

namespace Wcs

open StatMech.Lattice

open StatMech.Wad

open StatMech.Euc

open StatMech.Walls


theorem mem_toVtxFinset (K : Set (Site 2)) (hK : K.Finite) (p : ℤ × ℤ) :
    p ∈ toVtxFinset K hK ↔ siteToVtx.symm p ∈ K := by
  classical
  unfold toVtxFinset
  rw [Finset.mem_image]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [Set.Finite.mem_toFinset] at hs
    rwa [Equiv.symm_apply_apply]
  · intro h
    exact ⟨siteToVtx.symm p, by rw [Set.Finite.mem_toFinset]; exact h, by simp⟩


theorem siteToVtx_mem_toVtxFinset (K : Set (Site 2)) (hK : K.Finite) (s : Site 2) :
    siteToVtx s ∈ toVtxFinset K hK ↔ s ∈ K := by
  rw [mem_toVtxFinset, Equiv.symm_apply_apply]


end Wcs
end StatMech
