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
import Def.StatisticalMechanics.Code.Onsager.CellEulerFaithful.Part2


namespace StatMech.Onsager.CellEulerFaithful

open Finset SimpleGraph Set

open StatMech.Lattice StatMech.Euc StatMech.Wad

open StatMech.Onsager.CellCount StatMech.Onsager.CellEuler
  StatMech.Onsager.CellEulerBound StatMech.Onsager.WalkCellRegion
  StatMech.Onsager.WalkCellBoundary StatMech.Onsager.BaseCase


theorem occupiedFace_reachable_eq (S : Finset Cell) (c : Cell) (hc : c ∈ S) (g : Site 2)
    (hreach : (whb_faceRegion (imageGraph (cellSkeletonP S))).Reachable (cellFace c) g) :
    g = cellFace c := by
  obtain ⟨p⟩ := hreach
  cases p with
  | nil => rfl
  | cons hadj _ => exact absurd hadj (occupiedFace_isolated S c hc _)


theorem occupiedComponent_finite (S : Finset Cell) (c : Cell) (hc : c ∈ S) :
    (occupiedComponent S c).supp.Finite := by
  apply Set.Finite.subset (Set.finite_singleton (cellFace c))
  intro g hg
  have hbase : cellFace c ∈ (occupiedComponent S c).supp := by
    rw [ConnectedComponent.mem_supp_iff]
    rfl
  have hreach := (occupiedComponent S c).reachable_of_mem_supp hbase hg
  exact occupiedFace_reachable_eq S c hc g hreach


end StatMech.Onsager.CellEulerFaithful
