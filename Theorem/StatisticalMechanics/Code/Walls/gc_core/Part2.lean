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
import Def.StatisticalMechanics.Code.Walls.gc_core.Part2
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech.Walls

open StatMech.Ising StatMech.Sharpness

open StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem gc_ursell_xeqy_nonpos (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x : V) (hox : o ≠ x) :
    eg_ursell3 G β h o x x ≤ 0 := by
  
  
  
  have hsq : eg_ursell3 G β h o x x
      = -2 * isingExpectation G β h (fun s => spin s x) * cov2 G β h o x := by
    unfold eg_ursell3 cov2
    have h1 : isingExpectation G β h (fun s => spin s o * (spin s x * spin s x))
        = isingExpectation G β h (fun s => spin s o) := by
      congr 1; funext s; rw [spin_sq, mul_one]
    have h2 : isingExpectation G β h (fun s => spin s x * spin s x) = 1 :=
      expectation_spin_mul_self G β h x
    rw [h1, h2]; ring
  rw [hsq]
  have hspin : 0 ≤ isingExpectation G β h (fun s => spin s x) :=
    expectation_spin_nonneg G β h hβ hh x
  have hcov : 0 ≤ cov2 G β h o x := cov2_nonneg G β h hβ hh o x hox
  nlinarith [mul_nonneg hspin hcov]


theorem gc_ursell_nonpos_of_signDominance (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hsd : GHSSignDominance G β h o) (x y : V) :
    eg_ursell3 G β h o x y ≤ 0 := by
  by_cases hox : o = x
  · subst hox
    by_cases hoy : o = y
    · 
      subst hoy
      rw [ghc_ursell_degenerate]
      have hspin : 0 ≤ isingExpectation G β h (fun s => spin s o) :=
        expectation_spin_nonneg G β h hβ hh o
      have hsle : isingExpectation G β h (fun s => spin s o) ≤ 1 :=
        expectation_spin_le_one G β h o
      
      have hcov : 0 ≤ cov2 G β h o o := by
        unfold cov2
        rw [expectation_spin_mul_self]
        nlinarith [hspin, hsle]
      nlinarith [mul_nonneg hspin hcov]
    · 
      exact gc_ursell_nonpos_degenerate G β h hβ hh o y hoy
  · by_cases hoy : o = y
    · subst hoy
      
      rw [ghc_ursell_swap]
      exact gc_ursell_nonpos_degenerate G β h hβ hh o x hox
    · by_cases hxy : x = y
      · 
        subst hxy
        exact gc_ursell_xeqy_nonpos G β h hβ hh o x hox
      · exact hsd x y hox hoy hxy


theorem gc_ghs_concavity_of_signDominance (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hsd : GHSSignDominance G β h o) :
    GHSThreePointSym G β h o :=
  ghc_ghs_of_ursell_nonpos G β h o
    (fun x y => gc_ursell_nonpos_of_signDominance G β h hβ hh o hsd x y)


theorem gc_aizenman_barsky_of_signDominance (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) (J : ℝ)
    (hsd : GHSSignDominance G β h o)
    (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e
        = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
    bondEnergySusceptibility G β h o
      ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o :=
  aizenman_barsky_inequality G β h o J (gc_ghs_concavity_of_signDominance G β h hβ hh o hsd) hfactor


theorem gc_spinProd_triple {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    spinProd ({o, x, y} : Finset V) = (fun s => spin s o * (spin s x * spin s y)) := by
  funext s
  rw [spinProd, Finset.prod_insert (by simp [hox, hoy]),
    Finset.prod_insert (by simp [hxy]), Finset.prod_singleton]


theorem gc_ursell_currentSum_rep (β : ℝ) {o x y : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    eg_ursell3 G β 0 o x y
      = currentSum G β (fun _ => 1) {o, x, y} / currentSum G β (fun _ => 1) ∅
        - currentSum G β (fun _ => 1) {o} / currentSum G β (fun _ => 1) ∅
            * (currentSum G β (fun _ => 1) {x, y} / currentSum G β (fun _ => 1) ∅)
        - currentSum G β (fun _ => 1) {o, x} / currentSum G β (fun _ => 1) ∅
            * (currentSum G β (fun _ => 1) {y} / currentSum G β (fun _ => 1) ∅)
        - currentSum G β (fun _ => 1) {o, y} / currentSum G β (fun _ => 1) ∅
            * (currentSum G β (fun _ => 1) {x} / currentSum G β (fun _ => 1) ∅)
        + 2 * (currentSum G β (fun _ => 1) {o} / currentSum G β (fun _ => 1) ∅)
            * (currentSum G β (fun _ => 1) {x} / currentSum G β (fun _ => 1) ∅)
            * (currentSum G β (fun _ => 1) {y} / currentSum G β (fun _ => 1) ∅) := by
  
  have hoxy := gc_ergrep G β ({o, x, y} : Finset V)
  have ho := gc_ergrep G β ({o} : Finset V)
  have hx := gc_ergrep G β ({x} : Finset V)
  have hy := gc_ergrep G β ({y} : Finset V)
  have hoxe := gc_ergrep G β ({o, x} : Finset V)
  have hoye := gc_ergrep G β ({o, y} : Finset V)
  have hxye := gc_ergrep G β ({x, y} : Finset V)
  rw [gc_spinProd_triple hox hoy hxy] at hoxy
  rw [spinProd_singleton] at ho hx hy
  rw [spinProd_pair o x hox] at hoxe
  rw [spinProd_pair o y hoy] at hoye
  rw [spinProd_pair x y hxy] at hxye
  unfold eg_ursell3
  rw [hoxy, ho, hx, hy, hoxe, hoye, hxye]

end StatMech.Walls
