/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh3weightedcor3.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.Simon.Part3
import Theorem.StatisticalMechanics.Code.Walls.ghc_urselleqgap
import Theorem.StatisticalMechanics.Code.Walls.ghggrahamclose
import Theorem.StatisticalMechanics.Code.Walls.gh3weightedcor3
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]


def gh3_eq22_decomposition (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ) (o x y : V) : Prop :=
  ∃ surv dropA dropB : ℝ,
    eg_ursell3 G β h o x y = surv - 2 * dropA - 2 * dropB
      ∧ 0 ≤ dropA ∧ 0 ≤ dropB


def gh3_lemma1_finish (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ) (o x y : V) (surv : ℝ) :
    Prop := surv ≤ 0


end StatMech.Walls
