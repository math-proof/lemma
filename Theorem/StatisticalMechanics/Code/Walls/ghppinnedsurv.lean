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
import Def.StatisticalMechanics.Code.Walls.ghppinnedsurv
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


theorem ghp_survConcrete_eq (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ) (i j k : V) :
    ghp_survConcrete G β h i j k
      = StatMech.Ising.cov2 G β h i j * StatMech.Ising.cov2 G β h j k
        - StatMech.Walls.VBG.vbg_var (StatMech.Ising.isingProb G β h) (fun s => StatMech.Ising.spin s j)
            * StatMech.Ising.cov2 G β h i k := rfl


theorem ghp_surv_le_zero (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ) (hβ : 0 ≤ β) (i j k : V) :
    ghp_survConcrete G β h i j k ≤ 0 := by
  rw [ghp_survConcrete_eq]
  have := StatMech.Walls.VBG.vbg_cor1 G β h hβ i j k
  linarith


theorem ghp_ghs_of_pinned (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ) (hβ : 0 ≤ β)
    (o x y i j k : V) {dropA dropB : ℝ}
    (hident : eg_ursell3 G β h o x y = ghp_survConcrete G β h i j k - 2 * dropA - 2 * dropB)
    (hdropA : 0 ≤ dropA) (hdropB : 0 ≤ dropB) :
    eg_ursell3 G β h o x y ≤ 0 := by
  have hsurv : ghp_survConcrete G β h i j k ≤ 0 := ghp_surv_le_zero G β h hβ i j k
  linarith


end StatMech.Walls
