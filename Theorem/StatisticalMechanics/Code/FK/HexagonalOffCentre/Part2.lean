/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalOffCentre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriangularOffCentre.Part5
import Theorem.StatisticalMechanics.Code.FK.HexagonalSharpness.Part5
import Def.StatisticalMechanics.Code.FK.HexagonalOffCentre.Part4
open scoped BigOperators Classical
open Finset Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.FiniteGraphBoundaryDifferential

noncomputable section

theorem hexagonalReflect_adj (u v : HexVertex) :
    hexagonalGraph.Adj u v ↔
      hexagonalGraph.Adj (hexagonalReflect u) (hexagonalReflect v) := by
  rw [hexagonalGraph_adj, hexagonalGraph_adj]
  constructor
  · rintro (⟨hu, hv, i, h⟩ | ⟨hv, hu, i, h⟩)
    · refine Or.inr ⟨by simp [hexagonalReflect, hv],
          by simp [hexagonalReflect, hu], i, ?_⟩
      dsimp [hexagonalReflect]
      calc
        -u.1 - -v.1 = v.1 - u.1 := by abel
        _ = hexagonalStep i := h
    · refine Or.inl ⟨by simp [hexagonalReflect, hu],
          by simp [hexagonalReflect, hv], i, ?_⟩
      dsimp [hexagonalReflect]
      calc
        -v.1 - -u.1 = u.1 - v.1 := by abel
        _ = hexagonalStep i := h
  · rintro (⟨hu, hv, i, h⟩ | ⟨hv, hu, i, h⟩)
    · have hu' : u.2 = true := by
        cases hu0 : u.2 <;> simp_all [hexagonalReflect]
      have hv' : v.2 = false := by
        cases hv0 : v.2 <;> simp_all [hexagonalReflect]
      refine Or.inr ⟨hv', hu', i, ?_⟩
      dsimp [hexagonalReflect] at h
      calc
        u.1 - v.1 = -v.1 - -u.1 := by abel
        _ = hexagonalStep i := h
    · have hv' : v.2 = true := by
        cases hv0 : v.2 <;> simp_all [hexagonalReflect]
      have hu' : u.2 = false := by
        cases hu0 : u.2 <;> simp_all [hexagonalReflect]
      refine Or.inl ⟨hu', hv', i, ?_⟩
      dsimp [hexagonalReflect] at h
      calc
        v.1 - u.1 = -u.1 - -v.1 := by abel
        _ = hexagonalStep i := h

end
end StatMech.FK.PeriodicPlanar
