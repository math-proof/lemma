/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc83crosspairing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc82grahamgeometric.Part2
import Def.StatisticalMechanics.Code.Walls.gc83crosspairing.Part2
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.RandomCurrent StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem gc83_netNonpos_iff_threeGapNonpos (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    gc83_NetNonpos G β h o x y ↔ gc82_ThreeGapNonpos G β h o x y := by
  unfold gc83_NetNonpos gc82_ThreeGapNonpos
  constructor
  · intro hnet m
    rw [gc83_threeGap_eq_fam G β h o x y hox hoy hxy m]
    by_cases hm : gc83_fourMark G o x y m
    · rw [if_pos hm]; exact hnet m hm
    · rw [if_neg hm]
  · intro hsign m hm
    have := hsign m
    rw [gc83_threeGap_eq_fam G β h o x y hox hoy hxy m, if_pos hm] at this
    exact this


theorem gc83_ursell_nonpos_of_netNonpos (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hnet : gc83_NetNonpos G β h o x y)
    (hsupp : gc82_ThreeGapAllConnSupported G β h o x y) :
    eg_ursell3 G β h o x y ≤ 0 :=
  gc82_ursell_nonpos G β h o x y hox hoy hxy
    ((gc83_netNonpos_iff_threeGapNonpos G β h o x y hox hoy hxy).1 hnet) hsupp


end StatMech.Walls
