/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalOffCentre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriangularOffCentre.Part5
import Theorem.StatisticalMechanics.Code.FK.HexagonalSharpness.Part5
import Def.StatisticalMechanics.Code.FK.HexagonalOffCentre.Part5
open scoped BigOperators Classical
open Finset Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.FiniteGraphBoundaryDifferential

noncomputable section

theorem hexagonalTransEquiv_adj (R : Nat) (x : HexVertex)
    (u v : HexagonalBoxVertex R) :
    (hexagonalBoxGraph R).Adj u v ↔
      (hexagonalTransBoxGraph R x.1).Adj
        (hexagonalTransEquiv R x u)
        (hexagonalTransEquiv R x v) := by
  cases hx : x.2
  · simp only [hexagonalBoxGraph, hexagonalTransBoxGraph,
      SimpleGraph.comap_adj, hexagonalBoxEmbedding,
      hexagonalTransBoxEmbedding, hexagonalTransEquiv, hx,
      Bool.false_eq_true, ↓reduceIte]
    exact (hexagonal.shift_adj x.1 u.1 v.1).symm
  · have href := hexagonalReflect_adj (hexagonalBoxEmbedding R u)
        (hexagonalBoxEmbedding R v)
    have hshift := (hexagonal.shift_adj x.1
      (hexagonalReflect (hexagonalBoxEmbedding R u))
      (hexagonalReflect (hexagonalBoxEmbedding R v))).symm
    simp only [hexagonalBoxGraph, hexagonalTransBoxGraph,
      SimpleGraph.comap_adj, hexagonalBoxEmbedding,
      hexagonalTransBoxEmbedding, hexagonalTransEquiv, hx, ↓reduceIte]
    constructor
    · intro huv
      have hs := hshift.mp (href.mp huv)
      simpa [hexagonal, hexTranslate_apply, hexagonalReflect,
        sub_eq_add_neg, add_comm] using hs
    · intro huv
      have hs : hexagonalGraph.Adj
          (hexagonal.shift x.1 (hexagonalReflect u.1))
          (hexagonal.shift x.1 (hexagonalReflect v.1)) := by
        simpa [hexagonal, hexTranslate_apply, hexagonalReflect,
          sub_eq_add_neg, add_comm] using huv
      exact href.mpr (hshift.mpr hs)

@[simp] theorem hexagonalTransEquiv_center (R : Nat) (x : HexVertex) :
    hexagonalTransEquiv R x (hexagonalBoxRoot R) =
      hexagonalTransBoxCenter R x := by
  rcases x with ⟨x, b⟩
  cases b <;> apply Subtype.ext <;>
    simp [hexagonalTransEquiv, hexagonalBoxRoot, hexagonalTransBoxCenter]

theorem hexagonalTransEquiv_mem_shell (R k : Nat) (x : HexVertex)
    (y : HexagonalBoxVertex R) :
    hexagonalTransEquiv R x y ∈ hexagonalTransBoxShell R k x.1 ↔
      y ∈ hexagonalBoxShell R k := by
  cases hx : x.2 <;>
    simp [hexagonalTransEquiv, hx, hexagonalTransBoxShell, hexagonalBoxShell,
      sub_eq_add_neg, Int.natAbs_neg]

end
end StatMech.FK.PeriodicPlanar
