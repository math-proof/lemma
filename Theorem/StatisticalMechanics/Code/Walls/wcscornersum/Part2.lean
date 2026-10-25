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
import Def.StatisticalMechanics.Code.Walls.wcscornersum.Part2
open scoped BigOperators
open Finset
open SimpleGraph Function


namespace StatMech

namespace Wcs

open StatMech.Lattice

open StatMech.Wad

open StatMech.Euc

open StatMech.Walls


theorem mem_toVtxSet (K : Set (Site 2)) (p : ℤ × ℤ) :
    p ∈ toVtxSet K ↔ siteToVtx.symm p ∈ K := by
  unfold toVtxSet
  constructor
  · rintro ⟨s, hs, rfl⟩; rwa [Equiv.symm_apply_apply]
  · intro h; exact ⟨siteToVtx.symm p, h, by simp⟩

end Wcs
end StatMech
