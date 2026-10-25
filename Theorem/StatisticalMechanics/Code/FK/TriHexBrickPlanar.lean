/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickPlanar.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part15
import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
import Def.StatisticalMechanics.Code.FK.TriHexBrickPlanar
open SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice BeffaraDC


theorem hexagonalBrickVertex_injective :
    Function.Injective hexagonalBrickVertex := by
  rintro ⟨x, bx⟩ ⟨y, cy⟩ h
  cases bx <;> cases cy <;>
    simp [hexagonalBrickVertex, funext_iff] at h ⊢ <;> omega


theorem hexagonalBrickVertex_adj {u v : HexVertex}
    (huv : hexagonalGraph.Adj u v) :
    (hypercubicLattice 2).Adj
      (hexagonalBrickVertex u) (hexagonalBrickVertex v) := by
  rw [hexagonalGraph_adj] at huv
  rcases u with ⟨x, bx⟩
  rcases v with ⟨y, cy⟩
  rcases huv with ⟨rfl, rfl, i, hi⟩ | ⟨rfl, rfl, i, hi⟩ <;>
    rw [hypercubicLattice_adj] <;>
    fin_cases i <;>
    simp [hexagonalBrickVertex, hexagonalStep, funext_iff] at hi ⊢ <;>
    omega


end StatMech.FK.PeriodicPlanar
