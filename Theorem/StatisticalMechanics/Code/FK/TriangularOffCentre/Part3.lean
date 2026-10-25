/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularOffCentre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriangularSharpness.Part5
import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedDomainActive
import Def.StatisticalMechanics.Code.FK.TriangularOffCentre.Part3
open scoped BigOperators Classical
open Finset Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.FiniteGraphBoundaryDifferential

noncomputable section

theorem triangularTransEquiv_adj (R : Nat) (x : Site 2)
    (u v : TriangularBoxVertex R) :
    (triangularBoxGraph R).Adj u v ↔
      (triangularTransBoxGraph R x).Adj
        (StatMech.FK.fvs_transEquiv 2 R x u)
        (StatMech.FK.fvs_transEquiv 2 R x v) := by
  rw [triangularBoxGraph, triangularTransBoxGraph,
    SimpleGraph.comap_adj, SimpleGraph.comap_adj,
    StatMech.FK.fvs_transEquiv_val, StatMech.FK.fvs_transEquiv_val,
    triangularGraph_adj, triangularGraph_adj]
  unfold triangularAdj
  constructor
  · rintro ⟨i, h | h⟩
    · refine ⟨i, Or.inl ?_⟩
      calc
        (v.1 + x) - (u.1 + x) = v.1 - u.1 := by abel
        _ = triangularStep i := h
    · refine ⟨i, Or.inr ?_⟩
      calc
        (u.1 + x) - (v.1 + x) = u.1 - v.1 := by abel
        _ = triangularStep i := h
  · rintro ⟨i, h | h⟩
    · refine ⟨i, Or.inl ?_⟩
      calc
        v.1 - u.1 = (v.1 + x) - (u.1 + x) := by abel
        _ = triangularStep i := h
    · refine ⟨i, Or.inr ?_⟩
      calc
        u.1 - v.1 = (u.1 + x) - (v.1 + x) := by abel
        _ = triangularStep i := h

@[simp] theorem triangularTransEquiv_center (R : Nat) (x : Site 2) :
    StatMech.FK.fvs_transEquiv 2 R x (triangularBoxRoot R) =
      triangularTransBoxCenter R x := by
  apply Subtype.ext
  funext i
  simp [triangularBoxRoot, triangularTransBoxCenter]

theorem triangularTransEquiv_mem_shell (R k : Nat) (x : Site 2)
    (y : TriangularBoxVertex R) :
    StatMech.FK.fvs_transEquiv 2 R x y ∈ triangularTransBoxShell R k x ↔
      y ∈ triangularBoxShell R k := by
  simp [triangularTransBoxShell, triangularBoxShell,
    StatMech.FK.fvs_transEquiv_val]

end
end StatMech.FK.PeriodicPlanar
