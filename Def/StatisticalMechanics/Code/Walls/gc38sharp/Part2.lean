/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc38sharp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc37hdom.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc38sharp.Part2
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

open StatMech.Sharpness (ofEdgeFun weight currentSum sourcePairSum)

open StatMech.Sharpness.FluxEdgeCopy (Copy endsM endsM_not_isDiag sourcePairDisconnSum
  sourcePairDisconnSum_eq_edgecopy sourcePairSum_eq_edgecopy)


open StatMech.Sharpness.GhostCurrentRep (gcr_pairCount_empty gcr_pairCount_disconn
  gcr_summable_edgecopy gcr_summable_edgecopy_disconn)


def gc38_SharpGHSResidue (β h : ℝ) (o x y : V) : Prop :=
  gc37_U4 G β h o x y ≤ -2 * gc37_triple G β h o x y


end StatMech.Walls
