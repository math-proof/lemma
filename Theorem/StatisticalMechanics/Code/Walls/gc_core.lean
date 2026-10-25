/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Ising.AizenmanBarsky.Part5
import Theorem.StatisticalMechanics.Code.Ising.GHSThreePoint
import Theorem.StatisticalMechanics.Code.Walls.ghc_urselleqgap
import Theorem.StatisticalMechanics.Code.Walls.gc_ergrep
import Def.StatisticalMechanics.Code.Walls.gc_core
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech.Walls

open StatMech.Ising StatMech.Sharpness

open StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem gc_ursell_eq_lebowitz_plus_triple (β h : ℝ) (o x y : V) :
    eg_ursell3 G β h o x y
      = gc_lebowitzU4 G β h o x y
        + 2 * isingExpectation G β h (fun s => spin s o)
            * isingExpectation G β h (fun s => spin s x)
            * isingExpectation G β h (fun s => spin s y) := by
  unfold eg_ursell3 gc_lebowitzU4
  ring


theorem gc_triple_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V) :
    0 ≤ 2 * isingExpectation G β h (fun s => spin s o)
          * isingExpectation G β h (fun s => spin s x)
          * isingExpectation G β h (fun s => spin s y) := by
  have ho : 0 ≤ isingExpectation G β h (fun s => spin s o) :=
    expectation_spin_nonneg G β h hβ hh o
  have hx : 0 ≤ isingExpectation G β h (fun s => spin s x) :=
    expectation_spin_nonneg G β h hβ hh x
  have hy : 0 ≤ isingExpectation G β h (fun s => spin s y) :=
    expectation_spin_nonneg G β h hβ hh y
  have h2o : 0 ≤ 2 * isingExpectation G β h (fun s => spin s o) := by linarith
  exact mul_nonneg (mul_nonneg h2o hx) hy


theorem gc_lebowitz_le_ursell (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V) :
    gc_lebowitzU4 G β h o x y ≤ eg_ursell3 G β h o x y := by
  rw [gc_ursell_eq_lebowitz_plus_triple]
  have := gc_triple_nonneg G β h hβ hh o x y
  linarith


theorem gc_ursell_nonpos_degenerate (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (x y : V) (hxy : x ≠ y) :
    eg_ursell3 G β h x x y ≤ 0 :=
  ghc_ursell_nonpos_degenerate G β h hβ hh x y hxy


end StatMech.Walls
