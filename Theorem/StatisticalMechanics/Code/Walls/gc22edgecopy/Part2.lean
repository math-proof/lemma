/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc22edgecopy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc21fiberconn.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc20closure.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc19switching.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc18core.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc16core.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc15core.Part5
import Theorem.StatisticalMechanics.Code.Walls.gc7core
import Theorem.StatisticalMechanics.Code.Walls.gc6_munonneg
import Theorem.StatisticalMechanics.Code.Sharpness.Switching.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Ising.TwoReplicaWeighted.Part2
import Theorem.StatisticalMechanics.Code.Ising.HdomNativeWeight.Part3
import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
import Def.StatisticalMechanics.Code.Walls.gc22edgecopy
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


theorem gc22_cert_of_allConnResidue (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hres : gc22_AllConnResidue G β h o x y) :
    gc16_PerConfigCert G β h o x y := by
  intro m hm
  by_cases hOg : connP (posEdges (withGhost G).edgeFinset (ofEdgeFun (withGhost G) m)) (some o) none
  · exact hres m hm hOg
  · exact gc22_cert_nonpos_of_fullDisc G β h hβ hh o x y hox hoy hxy m hm hOg


theorem gc22_ursell_nonpos_of_allConnResidue (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hres : gc22_AllConnResidue G β h o x y) :
    eg_ursell3 G β h o x y ≤ 0 :=
  gc16_cert_closes_u3 G β h o x y hox hoy hxy
    (gc22_cert_of_allConnResidue G β h hβ hh o x y hox hoy hxy hres)


theorem gc22_ghs_of_allConnResidue (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V)
    (hres : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc22_AllConnResidue G β h o x y) :
    GHSThreePointSym G β h o :=
  gc16_ghs_of_cert G β h hβ hh o
    (fun x y hox hoy hxy =>
      gc22_cert_of_allConnResidue G β h hβ hh o x y hox hoy hxy (hres x y hox hoy hxy))


theorem gc22_aizenman_barsky_of_allConnResidue (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) (J : ℝ)
    (hres : ∀ x y : V, o ≠ x → o ≠ y → x ≠ y → gc22_AllConnResidue G β h o x y)
    (hfactor : ∑ e ∈ G.edgeFinset, ghsBoundSym G β h o e
        = J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o) :
    bondEnergySusceptibility G β h o
      ≤ J * (isingExpectation G β h (fun s => spin s o)) * susceptibility G β h o :=
  gc16_aizenman_barsky_of_cert G β h hβ hh o J
    (fun x y hox hoy hxy =>
      gc22_cert_of_allConnResidue G β h hβ hh o x y hox hoy hxy (hres x y hox hoy hxy))
    hfactor

end StatMech.Walls
