/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc29hdom.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc28ghsrigid
import Theorem.StatisticalMechanics.Code.Ising.TwoCurrentProbBound
import Theorem.StatisticalMechanics.Code.Ising.CrossClassHdom
import Theorem.StatisticalMechanics.Code.Ising.HdomMultiplicity.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc15core.Part5
import Def.StatisticalMechanics.Code.Walls.gc29hdom
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

open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem gc29_hdom_of_backboneReroute (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Sharpness.Current V))
    (B : Finset V) {o x y : V}
    (hres : gc29_BackboneReroute G β J M B o x y) :
    2 * (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m B)
      ≤ ∑ m ∈ M.filter (fun m => hnw_noneConn G m o x y), hnw_mass G β J m B := by
  obtain ⟨R, _hRnn, hlo, hhi⟩ := hres
  exact le_trans hlo hhi


theorem gc29_backboneReroute_of_hdom (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Sharpness.Current V)) (B : Finset V) {o x y : V}
    (hdom : 2 * (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m B)
      ≤ ∑ m ∈ M.filter (fun m => hnw_noneConn G m o x y), hnw_mass G β J m B) :
    gc29_BackboneReroute G β J M B o x y :=
  ⟨fun m => hnw_mass G β J m B, fun m => hnw_mass_nonneg G β J hβ hJ m B, hdom, le_refl _⟩


theorem gc29_native_gap_nonneg_of_backboneReroute (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Sharpness.Current V))
    (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (B : Finset V)
    (hm : ∀ m ∈ M, Sharpness.sources G m = B) {o x y : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) (hcoh : ∀ m ∈ M, hnw_coherent G m o x y)
    (hres : gc29_BackboneReroute G β J M B o x y) :
    0 ≤ ∑ m ∈ M, hnw_gap G β J m B o x y :=
  gc28_native_closure_of_hdom G β J M hnd B hm hox hoy hxy hcoh
    (gc29_hdom_of_backboneReroute G β J M B hres)


theorem gc29_backboneReroute_of_allConnMass_zero (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β)
    (hJ : ∀ e, 0 ≤ J e) (M : Finset (Sharpness.Current V)) (B : Finset V) {o x y : V}
    (hzero : (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m B) = 0) :
    gc29_BackboneReroute G β J M B o x y := by
  refine ⟨fun m => hnw_mass G β J m B, fun m => hnw_mass_nonneg G β J hβ hJ m B, ?_, le_refl _⟩
  rw [hzero]
  have : 0 ≤ ∑ m ∈ M.filter (fun m => hnw_noneConn G m o x y), hnw_mass G β J m B :=
    Finset.sum_nonneg (fun m _ => hnw_mass_nonneg G β J hβ hJ m B)
  linarith

end StatMech.Walls
