/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thinthickdichotomy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.jc_core
import Theorem.StatisticalMechanics.Code.Walls.jc_earanchor.Part2
import Structure.StatisticalMechanics.Code.Walls.jc2_thinthickdichotomy
open SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem jc2_topRowRun_thinThickDichotomy (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hrun : jc_IsTopRowRun K c len) : jc2_ThinThickDichotomy K c len where
  dichotomy hlen := jc2_thin_thick_dichotomy K c len hrun hlen
  len_zero_split h0 v hv hadj := by
    subst h0
    exact jc2_len_zero_right_or_down K c hrun v hv hadj


theorem jc2_thinThickDichotomy (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hrun : jc_IsTopRowRun K c len) : jc2_ThinThickDichotomy K c len :=
  jc2_topRowRun_thinThickDichotomy K c len hrun


theorem jc2_domino_thin_pendant :
    jc_IsPendantCell domino (jc2_rightEnd (![0, 0] : Site 2) 1) := by
  apply jc2_thin_pendant domino (![0, 0] : Site 2) 1 jc_domino_isTopRowRun (by norm_num)
  rw [jc2_rightEnd]
  apply not_mem_domino
  intro h
  rcases h with ⟨_, h1⟩ | ⟨_, h1⟩ <;>
    · revert h1
      simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
      omega


theorem jc2_unitCell_len_zero_split :
    jc2_ThinThickDichotomy unitCell (![0, 0] : Site 2) 0 :=
  jc2_thinThickDichotomy unitCell (![0, 0]) 0 jc_unitCell_isTopRowRun

end Walls
end StatMech
