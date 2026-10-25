/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualEventSetEquality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

variable {ω : ConfigSpace (Sym2 (Site 2))} {n : ℤ}


@[simp] theorem des_rot90Inv_zero (x : Site 2) : (rot90Inv x) 0 = x 1 := by
  simp [rot90Inv]

@[simp] theorem des_rot90Inv_one (x : Site 2) : (rot90Inv x) 1 = - x 0 := by
  simp [rot90Inv]


theorem des_rot90Inv_rect (n : ℤ) (x : Site 2) :
    x ∈ rect 0 n 0 n ↔ rot90Inv x ∈ rect 0 n (-n) 0 := by
  simp only [mem_rect, des_rot90Inv_zero, des_rot90Inv_one]
  constructor <;> intro h <;> exact ⟨by omega, by omega, by omega, by omega⟩


theorem des_rot90Inv_bottomSide (n : ℤ) (x : Site 2) :
    x ∈ bottomSide 0 n 0 n ↔ rot90Inv x ∈ leftSide 0 n (-n) 0 := by
  simp only [mem_bottomSide, mem_leftSide, mem_rect, des_rot90Inv_zero, des_rot90Inv_one]
  constructor <;> rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩ <;>
    exact ⟨⟨by omega, by omega, by omega, by omega⟩, by omega⟩


theorem des_rot90Inv_topSide (n : ℤ) (x : Site 2) :
    x ∈ topSide 0 n 0 n ↔ rot90Inv x ∈ rightSide 0 n (-n) 0 := by
  simp only [mem_topSide, mem_rightSide, mem_rect, des_rot90Inv_zero, des_rot90Inv_one]
  constructor <;> rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩ <;>
    exact ⟨⟨by omega, by omega, by omega, by omega⟩, by omega⟩


end Universality
end StatMech
