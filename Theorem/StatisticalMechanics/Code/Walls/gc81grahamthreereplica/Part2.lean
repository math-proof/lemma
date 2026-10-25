/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc81grahamthreereplica.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc25resummation.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc37hdom.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc80bookroute
import Theorem.StatisticalMechanics.Code.Walls.FaithfulnessAudit.Part2
import Def.StatisticalMechanics.Code.Walls.gc81grahamthreereplica.Part2
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


theorem gc81_grahamResummation (β h : ℝ) (o x y : V) :
    (gc15_Z0 G β h) ^ 3 * eg_ursell3 G β h o x y
      = -2 * gc81_grahamAllConnMass G β h o x y := by
  unfold gc81_grahamAllConnMass; ring


theorem gc81_ursell_nonpos_iff_grahamMass_nonneg (β h : ℝ) (o x y : V) :
    eg_ursell3 G β h o x y ≤ 0 ↔ 0 ≤ gc81_grahamAllConnMass G β h o x y := by
  have hZ : 0 < gc15_Z0 G β h := gc15_Z0_pos G β h
  have hZ3 : 0 < (gc15_Z0 G β h) ^ 3 := pow_pos hZ 3
  unfold gc81_grahamAllConnMass
  constructor
  · intro hu
    have : (gc15_Z0 G β h) ^ 3 * eg_ursell3 G β h o x y ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hZ3) hu
    nlinarith [this]
  · intro hd
    nlinarith [hd, hZ3]


theorem gc81_grahamMass_sub_leadingGap (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    gc81_grahamAllConnMass G β h o x y - gc25_nativeAllConnMass G β h o x y
      = - gc81_natRes_residual G β h o x y / 2 := by
  have hsum := gc15_u3_eq_tsum_threeGap G β h o x y hox hoy hxy
  have hdecomp := gc25_threeGap_sum_decomp G β h o x y hox hoy hxy
  
  have hpoly : (gc15_Z0 G β h) ^ 3 * eg_ursell3 G β h o x y
      = gc15_Z0 G β h * gc25_nativeAllConnMass G β h o x y
        - gc15_Z0 G β h * cs81 G β h {some o, some x} * cs81 G β h {some y, none}
        - gc15_Z0 G β h * cs81 G β h {some o, some y} * cs81 G β h {some x, none}
        + 2 * (cs81 G β h {some o, none} * cs81 G β h {some x, none}
            * cs81 G β h {some y, none}) := by
    unfold cs81
    rw [hsum, hdecomp]
  unfold gc81_grahamAllConnMass gc81_natRes_residual
  linear_combination (- hpoly / 2)


theorem gc81_grahamMass_eq_gap_iff (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    gc81_grahamAllConnMass G β h o x y = gc25_nativeAllConnMass G β h o x y
      ↔ gc25_NativeResummation G β h o x y := by
  rw [gc81_natRes_iff_residualZero G β h o x y hox hoy hxy]
  have hsub := gc81_grahamMass_sub_leadingGap G β h o x y hox hoy hxy
  constructor
  · intro heq
    have : gc81_grahamAllConnMass G β h o x y - gc25_nativeAllConnMass G β h o x y = 0 := by
      rw [heq]; ring
    rw [hsub] at this; linarith [this]
  · intro hR
    have : gc81_grahamAllConnMass G β h o x y - gc25_nativeAllConnMass G β h o x y = 0 := by
      rw [hsub, hR]; ring
    linarith [this]


theorem gc81_leadingGap_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V) :
    0 ≤ gc25_nativeAllConnMass G β h o x y :=
  gc25_nativeAllConnMass_nonneg G β h hβ hh o x y


end StatMech.Walls
