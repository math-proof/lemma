/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh9switchrearrange.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gh8weightedassembly.Part2
import Theorem.StatisticalMechanics.Code.Walls.gh5currentrep.Part3
import Theorem.StatisticalMechanics.Code.Walls.ghggrahamclose
import Theorem.StatisticalMechanics.Code.Walls.gc15core.Part5
import Theorem.StatisticalMechanics.Code.Walls.gh9switchrearrange
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
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.RandomCurrent StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls.GhcEqGap

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

variable {W : Type*} [DecidableEq W] [Fintype W]

variable {V : Type*} [Fintype V] [DecidableEq V]


def gh9_perSuperposition_weighted_eq22 (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ)
    (o x y : V) (ends : ι → Sym2 W) (m : Finset ι) (u u' : W) : Prop :=
  ∃ (surv : ℝ) (V₁ V₂ V₁' V₂' : Finset W) (wgtA diffA wgtB diffB : Finset ι → ℝ),
    (∀ A, 0 ≤ wgtA A) ∧ (∀ A, 0 ≤ diffA A) ∧ (∀ B, 0 ≤ wgtB B) ∧ (∀ B, 0 ≤ diffB B)
    ∧ eg_ursell3 G β h o x y
        = surv
          - 2 * (∑ A ∈ m.powerset, (gh5_complMassDecoupled ends m V₁ V₂ u A : ℝ) * wgtA A * diffA A)
          - 2 * (∑ B ∈ m.powerset, (gh5_complMassDecoupled ends m V₁' V₂' u' B : ℝ) * wgtB B * diffB B)
    ∧ surv ≤ 0


end StatMech.Walls
