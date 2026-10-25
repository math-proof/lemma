/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredWeights.Part4
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarDiagonalLimit
import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverageUpgrade
open Finset Set SimpleGraph Filter MeasureTheory Topology


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice Universality

noncomputable section

theorem triangular_mem_orbitBox_iff_box (n : Nat) (v : Site 2) :
    v ∈ triangular.orbitBox n ↔ v ∈ box 2 n := by
  rw [triangular.mem_orbitBox_iff]
  simp [triangular, siteTranslate_apply]


theorem hexagonal_mem_orbitBox_iff_box (n : Nat) (v : HexVertex) :
    v ∈ hexagonal.orbitBox n ↔ v.1 ∈ box 2 n := by
  rw [hexagonal.mem_orbitBox_iff]
  rcases v with ⟨v, b⟩
  cases b <;> simp [hexagonal, hexTranslate_apply]

theorem triHexPlanarCellTerminal_mem_box_succ
    (n : Nat) {z : Site 2} (hz : z ∈ box 2 n) (i : Fin 3) :
    triHexPlanarCellTerminal z i ∈ box 2 (n + 1) := by
  intro k
  fin_cases i <;> fin_cases k <;>
    simp [triHexPlanarCellTerminal, hexagonalStep] at hz ⊢ <;> omega

theorem triHexPlanarCellPredecessor_mem_box_succ
    (n : Nat) {v : Site 2} (hv : v ∈ box 2 n) :
    v - hexagonalStep 0 ∈ box 2 (n + 1) := by
  intro k
  fin_cases k <;> simp [hexagonalStep] at hv ⊢ <;> omega


end
end StatMech.FK.PeriodicPlanar
