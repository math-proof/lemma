/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc24deltabridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc23allconn.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc22edgecopy.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc15core.Part5
import Theorem.StatisticalMechanics.Code.Walls.gc10deltasupport
import Theorem.StatisticalMechanics.Code.Walls.gc10ensembleprob
import Theorem.StatisticalMechanics.Code.Sharpness.DeltaRewriteDichotomy.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Ising.CurrentWeight.Part2
import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
import Def.StatisticalMechanics.Code.Walls.gc24deltabridge.Part2
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


theorem gc24_ursell_nonpos_of_threeReplicaResummation (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hres : gc24_ThreeReplicaResummation G β h o x y) :
    eg_ursell3 G β h o x y ≤ 0 := by
  obtain ⟨ι, _, _, ends, F, hF, hnd, hsrc, hid⟩ := hres
  have hZ : 0 < gc15_Z0 G β h := gc15_Z0_pos G β h
  have hN : 0 ≤ gc10_allConnMass ends (some o) (some x) (some y) none F :=
    gc10_allConnMass_nonneg ends (some o) (some x) (some y) none F hF
  have hsum : ∑' m, gc15_threeGap G β h o x y m ≤ 0 := by rw [hid]; nlinarith [hN]
  have hpoly : (gc15_Z0 G β h) ^ 3 * eg_ursell3 G β h o x y ≤ 0 := by
    rw [gc15_u3_eq_tsum_threeGap G β h o x y hox hoy hxy]; exact hsum
  nlinarith [pow_pos hZ 3, hpoly]


theorem gc24_ghs_of_threeReplicaResummation (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hres : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc24_ThreeReplicaResummation G β h o x y) :
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
    · exact gc24_ursell_nonpos_of_threeReplicaResummation G β h o x y hox hoy hxy
        (hres x y hox hoy hxy)


theorem gc24_aizenman_barsky_of_threeReplicaResummation (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (o : V) (J : ℝ)
    (hres : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc24_ThreeReplicaResummation G β h o x y)
    (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e
        = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
    bondEnergySusceptibility G β h o
      ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o :=
  aizenman_barsky_inequality G β h o J
    (gc24_ghs_of_threeReplicaResummation G β h hβ hh o hres) hfactor


theorem gc24_backbone_not_signDefinite {ι : Type*} [DecidableEq ι] [Fintype ι]
    (ends : ι → Sym2 (Option V)) (m₁ m₂ : Finset ι) {o x y : V}
    (h₁ : connK ends m₁ (some x) (some y) ∧ connK ends m₁ (some o) (some y)
        ∧ connK ends m₁ (some o) (some x))
    (h₂ : ¬ connK ends m₂ (some x) (some y) ∧ ¬ connK ends m₂ (some o) (some y)
        ∧ ¬ connK ends m₂ (some o) (some x)) :
    asd_ghsBackboneFactor ends m₁ (some o) (some x) (some y) < 0
      ∧ 0 < asd_ghsBackboneFactor ends m₂ (some o) (some x) (some y) :=
  asd_ghsBackboneFactor_not_signDefinite ends m₁ m₂ h₁ h₂


theorem gc24_allConnMass_eq_caseA_plus_caseB {ι : Type*} [DecidableEq ι] [Fintype ι]
    (ends : ι → Sym2 (Option V)) (F : Finset ι → ℝ) {o x y : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hnd : ∀ i, ¬ (ends i).IsDiag)
    (hsrcSet : ∀ m : Finset ι, (¬ connK ends m (some o) none) →
        sources ends m = {some o, some x, some y, none}) :
    gc10_allConnMass ends (some o) (some x) (some y) none F
      = drd_pairSum ends ({some o, some x, some y, none} : Finset (Option V)) F
          (fun m => gc8_caseA ends (some o) (some x) (some y) none m)
        + drd_pairSum ends ({some o, some x, some y, none} : Finset (Option V)) F
          (fun m => gc8_caseB ends (some o) (some x) (some y) none m) :=
  gc10_allConnMass_eq_caseA_plus_caseB ends F (by simpa using hox) (by simpa using hoy) (by simp)
    (by simpa using hxy) (by simp) (by simp) hnd hsrcSet

end StatMech.Walls
