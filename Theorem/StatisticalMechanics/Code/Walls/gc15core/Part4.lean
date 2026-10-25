/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc15core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc10ghostfourpoint
import Theorem.StatisticalMechanics.Code.Walls.gc8Z0pos
import Def.StatisticalMechanics.Code.Walls.gc15core.Part3
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


variable (S : SimpleGraph V) [DecidableRel S.Adj]


theorem gc15_u3_eq_tsum_threeGap (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    (gc15_Z0 G β h) ^ 3 * eg_ursell3 G β h o x y
      = ∑' m, gc15_threeGap G β h o x y m := by
  obtain ⟨dOX, dOY, dOg, dXY, dXg, dYg⟩ := gc15_marks_distinct hox hoy hxy
  
  set J' := ghostCoupling h β (fun _ : Sym2 V => (1 : ℝ)) with hJ'
  
  rw [gc15_u3_currentSum_poly G β h o x y hox hoy hxy]
  rw [gc15_gquad o x y, gc15_gsingle o, gc15_gpair x y, gc15_gpair o x, gc15_gsingle y,
      gc15_gpair o y, gc15_gsingle x]
  
  
  
  have m0 := sourceTripleSum_eq_mul (withGhost G) β J' ∅ ∅
    ({some o, some x, some y, none} : Finset (Option V))
  have m1 := sourceTripleSum_eq_mul (withGhost G) β J' ∅ {some o, none} {some x, some y}
  have m2 := sourceTripleSum_eq_mul (withGhost G) β J' ∅ {some o, some x} {some y, none}
  have m3 := sourceTripleSum_eq_mul (withGhost G) β J' ∅ {some o, some y} {some x, none}
  have m4 := sourceTripleSum_eq_mul (withGhost G) β J' {some o, none} {some x, none} {some y, none}
  have hZ0 : gc15_Z0 G β h = currentSum (withGhost G) β J' ∅ := by rw [hJ', gc15_Z0]
  
  rw [gc15_sourceTripleSum_eq_tFiber (withGhost G) β J' ∅ ∅
        ({some o, some x, some y, none} : Finset (Option V))] at m0
  rw [gc15_sourceTripleSum_eq_tFiber (withGhost G) β J' ∅ {some o, none} {some x, some y}] at m1
  rw [gc15_sourceTripleSum_eq_tFiber (withGhost G) β J' ∅ {some o, some x} {some y, none}] at m2
  rw [gc15_sourceTripleSum_eq_tFiber (withGhost G) β J' ∅ {some o, some y} {some x, none}] at m3
  rw [gc15_sourceTripleSum_eq_tFiber (withGhost G) β J' {some o, none} {some x, none} {some y, none}] at m4
  
  rw [hZ0, pow_two]
  
  rw [show currentSum (withGhost G) β J' ∅ * currentSum (withGhost G) β J' ∅ *
        currentSum (withGhost G) β J' {some o, some x, some y, none}
      = ∑' m, gc15_tFiber (withGhost G) β J' ∅ ∅
          ({some o, some x, some y, none} : Finset (Option V)) m from m0.symm]
  rw [show currentSum (withGhost G) β J' ∅ * currentSum (withGhost G) β J' {some o, none}
        * currentSum (withGhost G) β J' {some x, some y}
      = ∑' m, gc15_tFiber (withGhost G) β J' ∅ {some o, none} {some x, some y} m from m1.symm]
  rw [show currentSum (withGhost G) β J' ∅ * currentSum (withGhost G) β J' {some o, some x}
        * currentSum (withGhost G) β J' {some y, none}
      = ∑' m, gc15_tFiber (withGhost G) β J' ∅ {some o, some x} {some y, none} m from m2.symm]
  rw [show currentSum (withGhost G) β J' ∅ * currentSum (withGhost G) β J' {some o, some y}
        * currentSum (withGhost G) β J' {some x, none}
      = ∑' m, gc15_tFiber (withGhost G) β J' ∅ {some o, some y} {some x, none} m from m3.symm]
  rw [show currentSum (withGhost G) β J' {some o, none} * currentSum (withGhost G) β J' {some x, none}
        * currentSum (withGhost G) β J' {some y, none}
      = ∑' m, gc15_tFiber (withGhost G) β J' {some o, none} {some x, none} {some y, none} m
      from m4.symm]
  
  have s0 := gc15_summable_tFiber (withGhost G) β J' ∅ ∅
    ({some o, some x, some y, none} : Finset (Option V))
  have s1 := gc15_summable_tFiber (withGhost G) β J' ∅ {some o, none} {some x, some y}
  have s2 := gc15_summable_tFiber (withGhost G) β J' ∅ {some o, some x} {some y, none}
  have s3 := gc15_summable_tFiber (withGhost G) β J' ∅ {some o, some y} {some x, none}
  have s4 := gc15_summable_tFiber (withGhost G) β J' {some o, none} {some x, none} {some y, none}
  rw [← Summable.tsum_sub s0 s1, ← Summable.tsum_sub (s0.sub s1) s2,
      ← Summable.tsum_sub ((s0.sub s1).sub s2) s3,
      ← tsum_mul_left,
      ← Summable.tsum_add (((s0.sub s1).sub s2).sub s3) (s4.mul_left 2)]
  refine tsum_congr (fun m => ?_)
  simp only [gc15_threeGap, hJ']


end StatMech.Walls
