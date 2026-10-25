/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh8weightedassembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gh6attach
import Theorem.StatisticalMechanics.Code.Walls.gh3weightedcor3.Part2
import Theorem.StatisticalMechanics.Code.Walls.gh7resum.Part2
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

open StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem gh8_weighted_drop_nonneg {ι : Type*} [DecidableEq ι] [Fintype ι]
    {W : Type*} [DecidableEq W] [Fintype W]
    (ends : ι → Sym2 W) (m : Finset ι) (V₁ V₂ : Finset W) (u : W)
    (wgtA diffA : Finset ι → ℝ) (hwgt : ∀ A, 0 ≤ wgtA A) (hdiff : ∀ A, 0 ≤ diffA A) :
    0 ≤ ∑ A ∈ m.powerset, (gh5_complMassDecoupled ends m V₁ V₂ u A : ℝ) * wgtA A * diffA A := by
  apply Finset.sum_nonneg
  intro A hA
  have hmass : (0 : ℝ) ≤ (gh5_complMassDecoupled ends m V₁ V₂ u A : ℝ) := by positivity
  have := hwgt A
  have := hdiff A
  positivity


end StatMech.Walls
