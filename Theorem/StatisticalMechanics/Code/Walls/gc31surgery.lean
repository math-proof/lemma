/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc31surgery.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc30reroute
import Theorem.StatisticalMechanics.Code.Ising.BackboneResummation.Part2
import Theorem.StatisticalMechanics.Code.Ising.BackboneExists
import Theorem.StatisticalMechanics.Code.Ising.HdomMultiplicity.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc7ghosteven
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

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem gc31_flux_monotone_not_noneConn (Ψ : Sharpness.Current V → Sharpness.Current V)
    (m : Sharpness.Current V) {o x y : V}
    (hmono : ∀ e, m e ≤ Ψ m e)
    (hall : hnw_allConn G m o x y) :
    ¬ hnw_noneConn G (Ψ m) o x y := by
  obtain ⟨hxy', _, _⟩ := hall
  intro hnone
  apply hnone.1
  refine connP_mono (Q := posEdges G.edgeFinset (Ψ m)) ?_ (connOdd_imp_connPos G.edgeFinset m hxy')
  intro e he
  rw [posEdges, Finset.mem_filter] at he ⊢
  exact ⟨he.1, le_trans he.2 (hmono e)⟩


theorem gc31_addBackbone_not_noneConn (m : Sharpness.Current V) (P : Finset (Sym2 V))
    {o x y : V} (hall : hnw_allConn G m o x y) :
    ¬ hnw_noneConn G (hmu_addBackbone P m) o x y :=
  gc31_flux_monotone_not_noneConn G (fun m' => hmu_addBackbone P m') m
    (fun e => by simp only [hmu_addBackbone_apply]; omega) hall


end StatMech.Walls
