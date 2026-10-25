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


namespace StatMech.Onsager.CellEulerFaithful

open Finset SimpleGraph Set

open StatMech.Lattice StatMech.Euc StatMech.Wad

open StatMech.Onsager.CellCount StatMech.Onsager.CellEuler
  StatMech.Onsager.CellEulerBound StatMech.Onsager.WalkCellRegion
  StatMech.Onsager.WalkCellBoundary StatMech.Onsager.BaseCase


def cellSkeleton (S : Finset Cell) : SimpleGraph {v // v ∈ regVerts S} where
  Adj a b := s(a.1, b.1) ∈ StatMech.Euc.regEdges S
  symm := by constructor; intro a b h; rwa [Sym2.eq_swap]
  loopless := ⟨by
    intro a h
    exact wad_edge_not_diag h (by simp)⟩


noncomputable def cellSkeletonP (S : Finset Cell) : PlanarZ2Subgraph where
  V := {v // v ∈ regVerts S}
  finV := inferInstance
  decV := inferInstance
  G := cellSkeleton S
  emb := ⟨fun v => ![v.1.1, v.1.2], by
    intro a b h
    apply Subtype.ext
    apply Prod.ext
    · exact congrFun h 0
    · exact congrFun h 1⟩
  isSub := by
    intro a b hab
    change s(a.1, b.1) ∈ StatMech.Euc.regEdges S at hab
    rw [StatMech.Euc.regEdges, Finset.mem_biUnion] at hab
    obtain ⟨c, _, he⟩ := hab
    obtain ⟨x, y⟩ := c
    simp only [StatMech.Euc.cellEdges, Finset.mem_insert, Finset.mem_singleton] at he
    rw [hypercubicLattice_adj, Fin.sum_univ_two]
    change (a.1.1 - b.1.1).natAbs + (a.1.2 - b.1.2).natAbs = 1
    rcases he with he | he | he | he <;> rw [Sym2.eq_iff] at he <;>
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      simp only [Prod.ext_iff, Prod.mk.injEq] at h1 h2 <;>
      (try simp only [Matrix.cons_val_zero, Matrix.cons_val_one]) <;> omega


end StatMech.Onsager.CellEulerFaithful
