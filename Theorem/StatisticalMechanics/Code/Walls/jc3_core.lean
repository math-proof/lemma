/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.jc2_core.Part3
import Theorem.StatisticalMechanics.Code.Walls.jc2_runframe.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc2_thinthickdichotomy.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc2_thinconn
import Theorem.StatisticalMechanics.Code.Walls.jc2_thickshelf.Part3
import Theorem.StatisticalMechanics.Code.Walls.jc3_earfootprint.Part3
import Theorem.StatisticalMechanics.Code.Walls.jc3_clipsymmdiff
import Theorem.StatisticalMechanics.Code.Walls.jc3_shelfcell
import Theorem.StatisticalMechanics.Code.Walls.jc3_tailturneq
import Theorem.StatisticalMechanics.Code.Lattice.BalancePreservingContraction.Part4
import Def.StatisticalMechanics.Code.Walls.jc3_core
open SimpleGraph Function Set


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem jc3_pendantClipMatch_of_splice (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (h : jc3_OrbitSpliceDatum K a r) :
    jc2_PendantClipMatch K a r := by
  obtain ⟨hne', a', m, m', n, hp, hp', htail, hbal⟩ := h
  refine ⟨hne', a', m, m', n, hp, hp', ?_, hbal⟩
  intro i hi
  obtain ⟨heq, hnp⟩ := htail i hi
  
  rw [heq]
  
  exact (bpc_turnZ_diff_singleton K r ((dartNext K)^[m + i] a.1) hnp).symm


end Walls
end StatMech
