/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghppinnedsurv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.vbgtriangle.Part3
import Theorem.StatisticalMechanics.Code.Walls.ghwweightedassembly
import Def.StatisticalMechanics.Code.Walls.ghppinnedsurv.Part2
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

open StatMech.Walls.VBG

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem ghp_ghs_of_eq22_pinned (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ) (hβ : 0 ≤ β)
    (o x y : V) (hres : ghp_eq22_pinned G β h o x y) :
    eg_ursell3 G β h o x y ≤ 0 := by
  obtain ⟨i, j, k, dropA, dropB, hdropA, hdropB, hident⟩ := hres
  exact ghp_ghs_of_pinned G β h hβ o x y i j k hident hdropA hdropB


theorem ghp_pinned_forces_ghs_all_fields (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ)
    (hβ : 0 ≤ β) (o x y : V) (hres : ghp_eq22_pinned G β h o x y) :
    eg_ursell3 G β h o x y ≤ 0 :=
  ghp_ghs_of_eq22_pinned G β h hβ o x y hres


theorem ghp_surv_is_twoPoint (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ) (v : V) :
    eg_ursell3 G β h v v v
      = 2 * (isingExpectation G β h (fun s => spin s v))^3
        - 2 * isingExpectation G β h (fun s => spin s v) :=
  StatMech.Walls.VBG.vbg_ghs_distinct G β h v


theorem ghp_eq22_pinned_of_ghs_dominated (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ)
    (o x y : V) (hdom : eg_ursell3 G β h o x y ≤ ghp_survConcrete G β h o o o) :
    ghp_eq22_pinned G β h o x y := by
  refine ⟨o, o, o, (ghp_survConcrete G β h o o o - eg_ursell3 G β h o x y) / 2, 0,
    by linarith, le_refl 0, ?_⟩
  ring


theorem ghp_status : True := trivial

end StatMech.Walls
