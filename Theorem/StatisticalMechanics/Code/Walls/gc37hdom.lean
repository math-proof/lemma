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
import Def.StatisticalMechanics.Code.Walls.gc37hdom
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


theorem gc37_ursell3_eq_U4_add_triple (β h : ℝ) (o x y : V) :
    eg_ursell3 G β h o x y = gc37_U4 G β h o x y + 2 * gc37_triple G β h o x y := by
  unfold eg_ursell3 gc37_U4 gc37_triple
  ring


theorem gc37_onePt_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (x : V) :
    0 ≤ isingExpectation G β h (fun s => spin s x) := by
  have hgks := gks_first G β h hβ hh {x}
  have hrw : (fun s => spin s x) = spinProd ({x} : Finset V) := by
    funext s; unfold spinProd; rw [Finset.prod_singleton]
  rw [hrw]; exact hgks


theorem gc37_triple_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V) :
    0 ≤ gc37_triple G β h o x y := by
  unfold gc37_triple
  exact mul_nonneg (mul_nonneg (gc37_onePt_nonneg G β h hβ hh o) (gc37_onePt_nonneg G β h hβ hh x))
    (gc37_onePt_nonneg G β h hβ hh y)


end StatMech.Walls
