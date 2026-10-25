/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StraightWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.StraightWalk.Part3
open Set
open SimpleGraph


namespace StatMech

namespace Lattice

theorem sw_lshape_mem_support (x0 y0 x1 y1 : ℤ) (z : Site 2) :
    z ∈ (sw_lshape x0 y0 x1 y1).support
      ↔ z ∈ (sw_horizSeg y0 x0 x1).support ∨ z ∈ (sw_vertSeg x1 y0 y1).support := by
  unfold sw_lshape
  exact Walk.mem_support_append_iff _ _


theorem sw_lshape_support_eq (x0 y0 x1 y1 : ℤ) (z : Site 2) :
    z ∈ (sw_lshape x0 y0 x1 y1).support
      ↔ (∃ t : ℤ, t ∈ Set.uIcc x0 x1 ∧ z = ![t, y0])
        ∨ (∃ t : ℤ, t ∈ Set.uIcc y0 y1 ∧ z = ![x1, t]) := by
  rw [sw_lshape_mem_support, sw_horizSeg_mem_support, sw_vertSeg_mem_support]

end Lattice
end StatMech
