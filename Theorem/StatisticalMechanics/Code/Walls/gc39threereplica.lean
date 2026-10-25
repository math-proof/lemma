/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc39threereplica.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc38sharp.Part3
import Def.StatisticalMechanics.Code.Walls.gc39threereplica
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

open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.FieldGhostDict

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


open StatMech.Sharpness (currentSum)


theorem gc39_sharpResidue_iff_allConn_ge_triple (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    gc38_SharpGHSResidue G β h o x y
      ↔ (gc15_Z0 G β h) ^ 2 * gc37_triple G β h o x y ≤ gc39_allConnSum G β h o x y := by
  unfold gc38_SharpGHSResidue gc39_allConnSum
  have hid := gc38_Z0sq_U4_eq_neg_two_allConn G β h hβ hh o x y hox hoy hxy
  have hZpos : 0 < gc15_Z0 G β h := gc15_Z0_pos G β h
  have hZ2 : 0 < (gc15_Z0 G β h) ^ 2 := by positivity
  constructor
  · intro hres
    nlinarith [hid, hres, hZ2]
  · intro hle
    nlinarith [hid, hle, hZ2]


theorem gc39_sharpResidue_of_csTriple_le (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hdom : gc39_csTriple G β h o x y ≤ gc15_Z0 G β h * gc39_allConnSum G β h o x y) :
    gc38_SharpGHSResidue G β h o x y := by
  rw [gc39_sharpResidue_iff_allConn_ge_triple G β h hβ hh o x y hox hoy hxy]
  have htriple := gc37_Z0cubed_triple G β h o x y
  have hZpos : 0 < gc15_Z0 G β h := gc15_Z0_pos G β h
  
  
  have hcs : gc39_csTriple G β h o x y = (gc15_Z0 G β h) ^ 3 * gc37_triple G β h o x y := by
    unfold gc39_csTriple
    rw [htriple]
    
    
    rw [gc15_gsingle o, gc15_gsingle x, gc15_gsingle y]
    rfl
  rw [hcs] at hdom
  
  have h2 : gc15_Z0 G β h * ((gc15_Z0 G β h) ^ 2 * gc37_triple G β h o x y)
      ≤ gc15_Z0 G β h * gc39_allConnSum G β h o x y := by nlinarith [hdom]
  exact le_of_mul_le_mul_left h2 hZpos


end StatMech.Walls
