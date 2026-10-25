/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc17core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc16core.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc10ghostfourpoint
import Theorem.StatisticalMechanics.Code.Ising.EnsembleGHS
import Theorem.StatisticalMechanics.Code.Ising.AizenmanBarsky.Part5
import Def.StatisticalMechanics.Code.Walls.gc17core
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.openClassical false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem gc17_ursell_nonpos_of_dichotomy (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hdich : gc17_AggregateDichotomy G β h o x y) :
    eg_ursell3 G β h o x y ≤ 0 := by
  unfold gc17_AggregateDichotomy at hdich
  rw [gc17_u3_eq_U4_plus_triple G β h o x y hox hoy hxy]
  linarith


theorem gc17_tsum_threeGap_nonpos_of_dichotomy (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hdich : gc17_AggregateDichotomy G β h o x y) :
    ∑' m, gc15_threeGap G β h o x y m ≤ 0 := by
  rw [gc17_tsum_threeGap_eq_u3 G β h o x y hox hoy hxy]
  have hZ : 0 < (gc15_Z0 G β h) ^ 3 := pow_pos (gc15_Z0_pos G β h) 3
  have hu3 : eg_ursell3 G β h o x y ≤ 0 :=
    gc17_ursell_nonpos_of_dichotomy G β h o x y hox hoy hxy hdich
  nlinarith [hZ, hu3]


theorem gc17_ghs_of_dichotomy (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hdich : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc17_AggregateDichotomy G β h o x y) :
    GHSThreePointSym G β h o := by
  rw [ghc_ghsSym_iff_ursell_nonpos]
  intro x y he
  have hxy : x ≠ y := by rw [SimpleGraph.mem_edgeFinset] at he; exact G.ne_of_adj he
  by_cases hox : o = x
  · subst hox
    exact ghc_ursell_nonpos_degenerate G β h hβ hh o y hxy
  · by_cases hoy : o = y
    · subst hoy
      rw [ghc_ursell_swap]
      exact ghc_ursell_nonpos_degenerate G β h hβ hh o x hox
    · exact gc17_ursell_nonpos_of_dichotomy G β h o x y hox hoy hxy (hdich x y hox hoy hxy)


theorem gc17_aizenman_barsky_of_dichotomy (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) (Jsum : ℝ)
    (hdich : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc17_AggregateDichotomy G β h o x y)
    (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e
        = Jsum * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
    bondEnergySusceptibility G β h o
      ≤ Jsum * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o :=
  aizenman_barsky_inequality G β h o Jsum (gc17_ghs_of_dichotomy G β h hβ hh o hdich) hfactor


theorem gc17_distinct_ursell_nonpos (β h : ℝ) (o : V)
    (hdich : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc17_AggregateDichotomy G β h o x y)
    {x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    eg_ursell3 G β h o x y ≤ 0 :=
  gc17_ursell_nonpos_of_dichotomy G β h o x y hox hoy hxy (hdich x y hox hoy hxy)

end StatMech.Walls
