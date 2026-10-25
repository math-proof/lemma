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
import Def.StatisticalMechanics.Code.Walls.gc15core.Part4
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


variable (S : SimpleGraph V) [DecidableRel S.Adj]


theorem gc15_ursell_nonpos_of_perConfig (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hsign : gc15_PerConfigUrsellSign G β h o x y) :
    eg_ursell3 G β h o x y ≤ 0 := by
  have hZ : 0 < gc15_Z0 G β h := gc15_Z0_pos G β h
  have hsum_nonpos : (gc15_Z0 G β h) ^ 3 * eg_ursell3 G β h o x y ≤ 0 := by
    rw [gc15_u3_eq_tsum_threeGap G β h o x y hox hoy hxy]
    
    have hsummable : Summable (gc15_threeGap G β h o x y) := by
      set J' := ghostCoupling h β (fun _ : Sym2 V => (1 : ℝ))
      have s0 := gc15_summable_tFiber (withGhost G) β J' ∅ ∅
        ({some o, some x, some y, none} : Finset (Option V))
      have s1 := gc15_summable_tFiber (withGhost G) β J' ∅ {some o, none} {some x, some y}
      have s2 := gc15_summable_tFiber (withGhost G) β J' ∅ {some o, some x} {some y, none}
      have s3 := gc15_summable_tFiber (withGhost G) β J' ∅ {some o, some y} {some x, none}
      have s4 := gc15_summable_tFiber (withGhost G) β J' {some o, none} {some x, none} {some y, none}
      exact (((s0.sub s1).sub s2).sub s3).add (s4.mul_left 2)
    exact tsum_nonpos (fun m => hsign m)
  nlinarith [pow_pos hZ 3, hsum_nonpos]


theorem gc15_ghs_of_perConfig (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hsign : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc15_PerConfigUrsellSign G β h o x y) :
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
    · 
      exact gc15_ursell_nonpos_of_perConfig G β h o x y hox hoy hxy (hsign x y hox hoy hxy)


theorem gc15_aizenman_barsky_of_perConfig (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) (J : ℝ)
    (hsign : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc15_PerConfigUrsellSign G β h o x y)
    (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e
        = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
    bondEnergySusceptibility G β h o
      ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o :=
  aizenman_barsky_inequality G β h o J (gc15_ghs_of_perConfig G β h hβ hh o hsign) hfactor


theorem gc15_distinct_ursell_nonpos (β h : ℝ) (o : V)
    (hsign : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc15_PerConfigUrsellSign G β h o x y)
    {x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    eg_ursell3 G β h o x y ≤ 0 :=
  gc15_ursell_nonpos_of_perConfig G β h o x y hox hoy hxy (hsign x y hox hoy hxy)


theorem gc15_threeGap_vanish (β h : ℝ) (o x y : V) (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (m : ↥(withGhost G).edgeFinset → ℕ)
    (hm : sources (withGhost G) (ofEdgeFun (withGhost G) m)
        ≠ ({some o, some x, some y, none} : Finset (Option V))) :
    gc15_threeGap G β h o x y m = 0 := by
  obtain ⟨dOX, dOY, dOg, dXY, dXg, dYg⟩ := gc15_marks_distinct hox hoy hxy
  unfold gc15_threeGap gc15_tFiber
  rw [gc15_sd0 (some o) (some x) (some y) none,
      gc15_sd1 (some o) (some x) (some y) none dOX dOY dOg dXY dXg dYg,
      gc15_sd2 (some o) (some x) (some y) none dOX dOY dOg dXY dXg dYg,
      gc15_sd3 (some o) (some x) (some y) none dOX dOY dOg dXY dXg dYg,
      gc15_sd4 (some o) (some x) (some y) none dOX dOY dOg dXY dXg dYg]
  rw [if_neg hm, if_neg hm, if_neg hm, if_neg hm, if_neg hm]
  ring

end StatMech.Walls
