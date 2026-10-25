/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf2faithcontract.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.baoallopen.Part2
import Theorem.StatisticalMechanics.Code.Walls.bcvcutvertex.Part3
import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
import Def.StatisticalMechanics.Code.Walls.bgf2faithcontract
open Set SimpleGraph Finset
open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation


theorem bgf2_update_inBox {L : ℕ} {c x : Site 2} (hx : bgf2_inBox L c x) (j : Fin 2) {v : ℤ}
    (hv : (v - c j).natAbs ≤ L) : bgf2_inBox L c (Function.update x j v) := by
  intro i
  by_cases hij : i = j
  · subst hij; rw [Function.update_self]; exact hv
  · rw [Function.update_of_ne hij]; exact hx i


theorem bgf2_mix_inBox {L : ℕ} {c x y : Site 2} (hx : bgf2_inBox L c x) (hy : bgf2_inBox L c y)
    (k : ℕ) : bgf2_inBox L c (mixSite x y k) := by
  intro i
  simp only [mixSite]
  by_cases h : (i : ℕ) < k
  · rw [if_pos h]; exact hy i
  · rw [if_neg h]; exact hx i


end StatMech.Walls
