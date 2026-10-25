/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc20closure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc19switching.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc18core.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc16core.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc15core.Part5
import Theorem.StatisticalMechanics.Code.Walls.gc7core
import Theorem.StatisticalMechanics.Code.Walls.gc6_munonneg
import Theorem.StatisticalMechanics.Code.Ising.HdomNativeWeight.Part3
import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
import Theorem.StatisticalMechanics.Code.Ising.TwoReplicaWeighted.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Def.StatisticalMechanics.Code.Walls.gc20closure
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

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem gc20_cert_of_trichotomy (β h : ℝ) (o x y : V) (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hreg : ∀ m : ↥(withGhost G).edgeFinset → ℕ,
      sources (withGhost G) (ofEdgeFun (withGhost G) m)
          = ({some o, some x, some y, none} : Finset (Option V)) →
      gc20_FiberConnRegime G β h o x y m) :
    gc16_PerConfigCert G β h o x y := by
  intro m hm
  have hog : (some o : Option V) ≠ none := by simp
  have hoxs : (some o : Option V) ≠ some x := by simpa using hox
  have hoys : (some o : Option V) ≠ some y := by simpa using hoy
  rcases hreg m hm with hall | hp1 | hp2
  · 
    obtain ⟨hOg, hOx, hOy, hcr1, hcr2⟩ := hall
    have hzero := gc19_cert_zero_of_allConn (withGhost G) β (ghostCoupling h β (fun _ => 1)) m
      (o := some o) (x := some x) (y := some y) (g := none)
      hog hoxs hoys (by simp) hOg hOx hOy hcr1 hcr2
    rw [hzero]
  · 
    obtain ⟨hdiscG, hdiscY, hOx⟩ := hp1
    rw [gc20_cert_zero_of_pairing1 G β h o x y hog hoxs hoys m hdiscG hdiscY hOx]
  · 
    obtain ⟨hdiscG, hdiscX, hOy⟩ := hp2
    rw [gc20_cert_zero_of_pairing2 G β h o x y hog hoxs hoys m hdiscG hdiscX hOy]


theorem gc20_ursell_nonpos_of_trichotomy (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hreg : ∀ m : ↥(withGhost G).edgeFinset → ℕ,
      sources (withGhost G) (ofEdgeFun (withGhost G) m)
          = ({some o, some x, some y, none} : Finset (Option V)) →
      gc20_FiberConnRegime G β h o x y m) :
    eg_ursell3 G β h o x y ≤ 0 :=
  gc16_cert_closes_u3 G β h o x y hox hoy hxy
    (gc20_cert_of_trichotomy G β h o x y hox hoy hxy hreg)


theorem gc20_ghs_of_trichotomy (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hreg : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → ∀ m : ↥(withGhost G).edgeFinset → ℕ,
      sources (withGhost G) (ofEdgeFun (withGhost G) m)
          = ({some o, some x, some y, none} : Finset (Option V)) →
      gc20_FiberConnRegime G β h o x y m) :
    GHSThreePointSym G β h o :=
  gc16_ghs_of_cert G β h hβ hh o
    (fun x y hox hoy hxy => gc20_cert_of_trichotomy G β h o x y hox hoy hxy (hreg x y hox hoy hxy))


theorem gc20_aizenman_barsky_of_trichotomy (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) (J : ℝ)
    (hreg : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → ∀ m : ↥(withGhost G).edgeFinset → ℕ,
      sources (withGhost G) (ofEdgeFun (withGhost G) m)
          = ({some o, some x, some y, none} : Finset (Option V)) →
      gc20_FiberConnRegime G β h o x y m)
    (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e
        = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
    bondEnergySusceptibility G β h o
      ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o :=
  gc16_aizenman_barsky_of_cert G β h hβ hh o J
    (fun x y hox hoy hxy => gc20_cert_of_trichotomy G β h o x y hox hoy hxy (hreg x y hox hoy hxy))
    hfactor

end StatMech.Walls
