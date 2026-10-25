/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryProfile.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.ABMeanfieldGhost
import Theorem.StatisticalMechanics.Code.Sharpness.CToOneLattice.Part4
import Def.StatisticalMechanics.Code.Sharpness.ABBoundaryProfile
open Finset Set SimpleGraph


namespace StatMech

namespace Sharpness

open ConfigSpace RandomCurrent Lattice


@[simp] theorem none_mem_abbTarget (d n : Nat) :
    none ∈ abbTarget d n := Or.inl rfl

theorem some_mem_abbTarget_iff (d n : Nat) (x : sctBox d n) :
    some x ∈ abbTarget d n ↔ (x : Site d) ∈ vertexBoundary d n := by
  constructor
  · rintro (h | ⟨y, hxy, hy⟩)
    · simp at h
    · exact Option.some.inj hxy ▸ hy
  · intro hx
    exact Or.inr ⟨x, rfl, hx⟩


end Sharpness
end StatMech
