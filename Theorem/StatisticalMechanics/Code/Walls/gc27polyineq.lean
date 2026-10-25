/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc27polyineq.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc25resummation.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc24deltabridge.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc15core.Part5
import Def.StatisticalMechanics.Code.Walls.gc27polyineq
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

open StatMech.Sharpness.RandomCurrent StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem gc27_tsumThreeGap_nonpos_iff_polyIneq (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    (∑' m, gc15_threeGap G β h o x y m) ≤ 0 ↔ gc27_GHSPolyIneq G β h o x y := by
  rw [gc25_threeGap_sum_decomp G β h o x y hox hoy hxy]
  unfold gc27_GHSPolyIneq
  constructor <;> intro hh <;> linarith [hh]


theorem gc27_ghs_iff_polyIneq (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    eg_ursell3 G β h o x y ≤ 0 ↔ gc27_GHSPolyIneq G β h o x y := by
  have hZ : 0 < gc15_Z0 G β h := gc15_Z0_pos G β h
  rw [← gc27_tsumThreeGap_nonpos_iff_polyIneq G β h o x y hox hoy hxy,
      ← gc15_u3_eq_tsum_threeGap G β h o x y hox hoy hxy]
  constructor
  · intro hu; nlinarith [pow_pos hZ 3, hu]
  · intro hs; nlinarith [pow_pos hZ 3, hs]


theorem gc27_polyIneq_closes_ghs (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hpoly : gc27_GHSPolyIneq G β h o x y) :
    eg_ursell3 G β h o x y ≤ 0 :=
  (gc27_ghs_iff_polyIneq G β h o x y hox hoy hxy).mpr hpoly


theorem gc27_ghs_of_polyIneq (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hpoly : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc27_GHSPolyIneq G β h o x y) :
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
    · exact gc27_polyIneq_closes_ghs G β h o x y hox hoy hxy (hpoly x y hox hoy hxy)


theorem gc27_aizenman_barsky_of_polyIneq (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) (J : ℝ)
    (hpoly : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc27_GHSPolyIneq G β h o x y)
    (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e
        = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
    bondEnergySusceptibility G β h o
      ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o :=
  aizenman_barsky_inequality G β h o J (gc27_ghs_of_polyIneq G β h hβ hh o hpoly) hfactor


theorem gc27_polyIneq_of_nativeResummation (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hres : gc25_NativeResummation G β h o x y) :
    gc27_GHSPolyIneq G β h o x y := by
  rw [← gc27_tsumThreeGap_nonpos_iff_polyIneq G β h o x y hox hoy hxy]
  have hN : 0 ≤ gc25_nativeAllConnMass G β h o x y :=
    gc25_nativeAllConnMass_nonneg G β h hβ hh o x y
  rw [hres]; nlinarith [hN]


end StatMech.Walls
