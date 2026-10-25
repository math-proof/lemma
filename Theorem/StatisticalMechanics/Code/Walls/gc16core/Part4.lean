/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc16core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc15core.Part5
import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
import Def.StatisticalMechanics.Code.Walls.gc16core.Part4
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.show false
set_option linter.style.openClassical false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

variable (S : SimpleGraph V) [DecidableRel S.Adj]


theorem gc16_perConfigSign_of_cert (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hcert : gc16_PerConfigCert G β h o x y) :
    gc15_PerConfigUrsellSign G β h o x y := by
  intro m
  by_cases hm : sources (withGhost G) (ofEdgeFun (withGhost G) m)
      = ({some o, some x, some y, none} : Finset (Option V))
  · rw [gc16_threeGap_eq_gated G β h o x y hox hoy hxy m hm]
    exact hcert m hm
  · exact gc16_perConfig_off_boundary G β h o x y hox hoy hxy m hm


theorem gc16_cert_closes_u3 (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hcert : gc16_PerConfigCert G β h o x y) :
    eg_ursell3 G β h o x y ≤ 0 :=
  gc15_ursell_nonpos_of_perConfig G β h o x y hox hoy hxy
    (gc16_perConfigSign_of_cert G β h o x y hox hoy hxy hcert)


theorem gc16_ghs_of_cert (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hcert : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc16_PerConfigCert G β h o x y) :
    GHSThreePointSym G β h o :=
  gc15_ghs_of_perConfig G β h hβ hh o
    (fun x y hox hoy hxy => gc16_perConfigSign_of_cert G β h o x y hox hoy hxy (hcert x y hox hoy hxy))


theorem gc16_aizenman_barsky_of_cert (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) (J : ℝ)
    (hcert : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc16_PerConfigCert G β h o x y)
    (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e
        = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
    bondEnergySusceptibility G β h o
      ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o :=
  gc15_aizenman_barsky_of_perConfig G β h hβ hh o J
    (fun x y hox hoy hxy => gc16_perConfigSign_of_cert G β h o x y hox hoy hxy (hcert x y hox hoy hxy))
    hfactor


theorem gc16_cert_of_perConfigSign (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hsign : gc15_PerConfigUrsellSign G β h o x y) :
    gc16_PerConfigCert G β h o x y := by
  intro m hm
  have h1 := hsign m
  rwa [gc16_threeGap_eq_gated G β h o x y hox hoy hxy m hm] at h1


theorem gc16_cert_iff_perConfigSign (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    gc16_PerConfigCert G β h o x y ↔ gc15_PerConfigUrsellSign G β h o x y :=
  ⟨gc16_perConfigSign_of_cert G β h o x y hox hoy hxy,
   gc16_cert_of_perConfigSign G β h o x y hox hoy hxy⟩

end StatMech.Walls
