/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc37hdom.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc24deltabridge.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc28ghsrigid
import Theorem.StatisticalMechanics.Code.Walls.ghc_urselleqgap
import Theorem.StatisticalMechanics.Code.Walls.FaithfulnessAudit.Part2
import Theorem.StatisticalMechanics.Code.Ising.CurrentWeight.Part2
import Def.StatisticalMechanics.Code.Walls.gc37hdom.Part4
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


theorem gc37_U4_nonpos_of_connRep (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hrep : gc37_U4a_connRep G β h o x y) :
    gc37_U4 G β h o x y ≤ 0 := by
  unfold gc37_U4a_connRep at hrep
  have hZpos : 0 < gc15_Z0 G β h := gc15_Z0_pos G β h
  have hZ2 : 0 < (gc15_Z0 G β h) ^ 2 := by positivity
  have hJnn : ∀ e, (0 : ℝ) ≤ ghostCoupling h β (fun _ => 1) e :=
    gc6_ghostCoupling_nonneg (V := V) β h hh
  have hconn := gc37_sourcePairConnSum_nonneg (withGhost G) β (ghostCoupling h β (fun _ => 1))
    hβ hJnn ({some o, some x} : Finset (Option V)) ({some y, none} : Finset (Option V))
    (some o) (some y)
  
  nlinarith [hrep, hconn, hZ2]


theorem gc37_twoReplica_U4_insufficient :
    ∃ a b : ℝ, a ≤ 0 ∧ 0 ≤ b ∧ 0 < a + 2 * b := by
  exact ⟨-1, 1, by norm_num, by norm_num, by norm_num⟩


theorem gc37_ursell3_nonpos_iff_sharp (β h : ℝ) (o x y : V) :
    eg_ursell3 G β h o x y ≤ 0
      ↔ gc37_U4 G β h o x y ≤ -2 * gc37_triple G β h o x y := by
  rw [gc37_ursell3_eq_U4_add_triple]
  constructor
  · intro hle; linarith
  · intro hle; linarith


theorem gc37_ursell3_nonpos_of_sharp (β h : ℝ) (o x y : V)
    (hsharp : gc37_U4 G β h o x y ≤ -2 * gc37_triple G β h o x y) :
    eg_ursell3 G β h o x y ≤ 0 :=
  (gc37_ursell3_nonpos_iff_sharp G β h o x y).mpr hsharp


theorem gc37_U4_eq_neg_two_triple_at_zero (β : ℝ) (o x y : V) :
    gc37_U4 G β 0 o x y = -2 * gc37_triple G β 0 o x y := by
  have h0 := fa_ghs_ursell3_h0_eq_zero G β o x y
  have hdecomp := gc37_ursell3_eq_U4_add_triple G β 0 o x y
  rw [h0] at hdecomp
  linarith

end StatMech.Walls
