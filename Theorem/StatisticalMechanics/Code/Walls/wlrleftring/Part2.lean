/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wlrleftring.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.InsideConnected.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeometricFaces.Part2
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Walls.wnbenoboundedeven
import Theorem.StatisticalMechanics.Code.Walls.wchcovering.Part3
import Theorem.StatisticalMechanics.Code.Walls.wicinterior.Part3
import Def.StatisticalMechanics.Code.Walls.wlrleftring
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

variable {a : Site 2}


theorem wlr_leftBoundary_subset_innerRing (Vc : (hypercubicLattice 2).Walk a a) :
    wic_leftBoundary Vc ⊆ wlr_innerRing Vc := by
  rintro w ⟨hint, hoff, hwest⟩
  refine ⟨hint, hoff, (![w 0 - 1, w 1] : Site 2), ?_, hwest⟩
  have : w = (![w 0, w 1] : Site 2) := (wic_eta w).symm
  rw [this]
  simp [hypercubicLattice_adj, Fin.sum_univ_two]


end Lattice
end StatMech
