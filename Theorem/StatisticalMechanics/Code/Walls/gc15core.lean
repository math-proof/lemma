/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc15core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc10ghostfourpoint
import Theorem.StatisticalMechanics.Code.Walls.gc8Z0pos
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem gc15_sd0 {W : Type*} [DecidableEq W] (O X Y g : W) :
    (∅ : Finset W) ∆ (∅ : Finset W) ∆ {O, X, Y, g} = {O, X, Y, g} := by simp


theorem gc15_sd1 {W : Type*} [DecidableEq W] (O X Y g : W)
    (hOX : O ≠ X) (hOY : O ≠ Y) (hOg : O ≠ g) (hXY : X ≠ Y) (hXg : X ≠ g) (hYg : Y ≠ g) :
    (∅ : Finset W) ∆ {O, g} ∆ {X, Y} = {O, X, Y, g} := by
  ext a
  simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  by_cases h1 : a = O <;> by_cases h2 : a = X <;> by_cases h3 : a = Y <;> by_cases h4 : a = g <;>
    subst_vars <;> simp_all


theorem gc15_sd2 {W : Type*} [DecidableEq W] (O X Y g : W)
    (hOX : O ≠ X) (hOY : O ≠ Y) (hOg : O ≠ g) (hXY : X ≠ Y) (hXg : X ≠ g) (hYg : Y ≠ g) :
    (∅ : Finset W) ∆ {O, X} ∆ {Y, g} = {O, X, Y, g} := by
  ext a
  simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  by_cases h1 : a = O <;> by_cases h2 : a = X <;> by_cases h3 : a = Y <;> by_cases h4 : a = g <;>
    subst_vars <;> simp_all


theorem gc15_sd3 {W : Type*} [DecidableEq W] (O X Y g : W)
    (hOX : O ≠ X) (hOY : O ≠ Y) (hOg : O ≠ g) (hXY : X ≠ Y) (hXg : X ≠ g) (hYg : Y ≠ g) :
    (∅ : Finset W) ∆ {O, Y} ∆ {X, g} = {O, X, Y, g} := by
  ext a
  simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  by_cases h1 : a = O <;> by_cases h2 : a = X <;> by_cases h3 : a = Y <;> by_cases h4 : a = g <;>
    subst_vars <;> simp_all


theorem gc15_sd4 {W : Type*} [DecidableEq W] (O X Y g : W)
    (hOX : O ≠ X) (hOY : O ≠ Y) (hOg : O ≠ g) (hXY : X ≠ Y) (hXg : X ≠ g) (hYg : Y ≠ g) :
    ({O, g} : Finset W) ∆ {X, g} ∆ {Y, g} = {O, X, Y, g} := by
  ext a
  simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  by_cases h1 : a = O <;> by_cases h2 : a = X <;> by_cases h3 : a = Y <;> by_cases h4 : a = g <;>
    subst_vars <;> simp_all


end StatMech.Walls
