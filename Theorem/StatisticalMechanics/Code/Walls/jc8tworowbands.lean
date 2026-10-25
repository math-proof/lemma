/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8tworowbands.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.jc7core.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc7loopiscycle
import Theorem.StatisticalMechanics.Code.Walls.jc7loopseparates.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc7ivtnohop
import Theorem.StatisticalMechanics.Code.Walls.jc7getverteqdartface
import Theorem.StatisticalMechanics.Code.Walls.jc5_core.Part2
import Theorem.StatisticalMechanics.Code.Lattice.OrbitLoopBridge
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Def.StatisticalMechanics.Code.Walls.jc8tworowbands
open SimpleGraph Function Set


namespace StatMech

namespace Walls

open StatMech.Lattice


@[simp] theorem jc8_mem_descentBand (r x : Site 2) :
    x ∈ jc8_descentBand r ↔ x 1 ≤ r 1 - 2 := Iff.rfl


@[simp] theorem jc8_mem_touchingBand (r x : Site 2) :
    x ∈ jc8_touchingBand r ↔ r 1 - 1 ≤ x 1 := Iff.rfl


theorem jc8_descentBand_below_shelf (r x : Site 2) (hx : x ∈ jc8_descentBand r) :
    x 1 < jc8_shelfRow r := by
  rw [jc8_mem_descentBand] at hx
  unfold jc8_shelfRow
  omega


theorem jc8_touchingBand_above_shelf (r x : Site 2) (hx : x ∈ jc8_touchingBand r) :
    jc8_shelfRow r ≤ x 1 := by
  rw [jc8_mem_touchingBand] at hx
  unfold jc8_shelfRow
  omega


theorem jc8_band_separation (r u v : Site 2)
    (hu : u 1 ≤ r 1 - 2) (hv : r 1 - 1 ≤ v 1) :
    u 1 < v 1 := by omega


theorem jc8_band_ne (r u v : Site 2)
    (hu : u 1 ≤ r 1 - 2) (hv : r 1 - 1 ≤ v 1) :
    u ≠ v := by
  intro heq
  have : u 1 < v 1 := jc8_band_separation r u v hu hv
  rw [heq] at this
  exact lt_irrefl _ this


theorem jc8_bands_disjoint (r : Site 2) :
    Disjoint (jc8_descentBand r) (jc8_touchingBand r) := by
  rw [Set.disjoint_left]
  intro x hxd hxt
  rw [jc8_mem_descentBand] at hxd
  rw [jc8_mem_touchingBand] at hxt
  omega


theorem jc8_band_separation_mem (r u v : Site 2)
    (hu : u ∈ jc8_descentBand r) (hv : v ∈ jc8_touchingBand r) :
    u 1 < v 1 ∧ u ≠ v := by
  rw [jc8_mem_descentBand] at hu
  rw [jc8_mem_touchingBand] at hv
  exact ⟨jc8_band_separation r u v hu hv, jc8_band_ne r u v hu hv⟩


end Walls
end StatMech
