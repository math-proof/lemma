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
import Def.StatisticalMechanics.Code.Onsager.CellEulerFaithful.Part3


namespace StatMech.Onsager.CellEulerFaithful

open Finset SimpleGraph Set

open StatMech.Lattice StatMech.Euc StatMech.Wad

open StatMech.Onsager.CellCount StatMech.Onsager.CellEuler
  StatMech.Onsager.CellEulerBound StatMech.Onsager.WalkCellRegion
  StatMech.Onsager.WalkCellBoundary StatMech.Onsager.BaseCase


theorem occupiedBoundedFace_injective (S : Finset Cell) :
    Function.Injective (occupiedBoundedFace S) := by
  intro c d h
  have hcomp : occupiedComponent S c.1 = occupiedComponent S d.1 := congrArg Subtype.val h
  have hreach : (whb_faceRegion (imageGraph (cellSkeletonP S))).Reachable
      (cellFace c.1) (cellFace d.1) := ConnectedComponent.eq.mp hcomp
  have hface : cellFace d.1 = cellFace c.1 :=
    occupiedFace_reachable_eq S c.1 c.2 (cellFace d.1) hreach
  exact Subtype.ext (cellFace.injective hface.symm)


theorem card_le_cellSkeleton_nullity (S : Finset Cell) :
    S.card ≤ nullity (cellSkeletonP S).G := by
  have hle := Nat.card_le_card_of_injective (occupiedBoundedFace S)
    (occupiedBoundedFace_injective S)
  rw [Nat.card_eq_fintype_card, Fintype.card_coe,
    jcb_boundedRegion_card_eq_nullity] at hle
  exact hle


theorem mem_cellSkeleton_edgeSet_iff (S : Finset Cell)
    (e : Sym2 {v // v ∈ regVerts S}) :
    e ∈ (cellSkeleton S).edgeSet ↔
      Sym2.map Subtype.val e ∈ StatMech.Euc.regEdges S := by
  induction e with
  | h a b => rfl

end StatMech.Onsager.CellEulerFaithful
