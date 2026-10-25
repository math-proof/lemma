/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEulerFaithful.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.WalkCellBoundary
import Theorem.StatisticalMechanics.Code.Lattice.JordanClusterBridge.Part8
import Def.StatisticalMechanics.Code.Onsager.CellEulerFaithful.Part4


namespace StatMech.Onsager.CellEulerFaithful

open Finset SimpleGraph Set

open StatMech.Lattice StatMech.Euc StatMech.Wad

open StatMech.Onsager.CellCount StatMech.Onsager.CellEuler
  StatMech.Onsager.CellEulerBound StatMech.Onsager.WalkCellRegion
  StatMech.Onsager.WalkCellBoundary StatMech.Onsager.BaseCase


theorem card_cellSkeleton_edges (S : Finset Cell) :
    Nat.card (cellSkeleton S).edgeSet = (StatMech.Euc.regEdges S).card := by
  rw [Nat.card_congr (cellSkeletonEdgeEquiv S), Nat.card_eq_fintype_card, Fintype.card_coe]

theorem card_cellSkeleton_vertices (S : Finset Cell) :
    Nat.card {v // v ∈ regVerts S} = (regVerts S).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]


theorem eulerChar_le_one_of_skeleton_connected (S : Finset Cell)
    (hconn : (cellSkeleton S).Connected) : eulerChar S ≤ 1 := by
  have hnull := card_le_cellSkeleton_nullity S
  have hcomp : Nat.card (cellSkeleton S).ConnectedComponent = 1 :=
    card_components_eq_one_of_connected hconn
  have hvertices := card_cellSkeleton_vertices S
  have hedges := card_cellSkeleton_edges S
  have hedges' : (cellSkeleton S).edgeSet.ncard =
      (StatMech.Euc.regEdges S).card := by
    rw [← Nat.card_coe_set_eq, hedges]
  have htree := hconn.card_vert_le_card_edgeSet_add_one
  rw [hvertices, hedges] at htree
  change S.card ≤ nullity (cellSkeleton S) at hnull
  unfold nullity at hnull
  rw [hcomp, hvertices, hedges'] at hnull
  rw [eulerChar_eq_regChi]
  unfold regChi
  push_cast
  omega


end StatMech.Onsager.CellEulerFaithful
