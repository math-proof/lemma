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
import Def.StatisticalMechanics.Code.Onsager.CellEulerFaithful.Part5


namespace StatMech.Onsager.CellEulerFaithful

open Finset SimpleGraph Set

open StatMech.Lattice StatMech.Euc StatMech.Wad

open StatMech.Onsager.CellCount StatMech.Onsager.CellEuler
  StatMech.Onsager.CellEulerBound StatMech.Onsager.WalkCellRegion
  StatMech.Onsager.WalkCellBoundary StatMech.Onsager.BaseCase


theorem corner_reachable_lowerLeft (S : Finset Cell) (c : Cell) (hc : c ∈ S)
    (v : Vtx) (hv : v ∈ StatMech.Euc.cellVerts c) :
    (cellSkeleton S).Reachable (skeletonVertexOfCorner S c hc v hv)
      (skeletonVertexOfCorner S c hc c (by
        obtain ⟨x, y⟩ := c
        simp [StatMech.Euc.cellVerts])) := by
  obtain ⟨x, y⟩ := c
  have hedge (a b : Vtx) (he : s(a, b) ∈ StatMech.Euc.cellEdges (x, y)) :
      (cellSkeleton S).Adj
        (skeletonVertexOfCorner S (x, y) hc a (by
          have ha := wad_edge_mem_regVerts (K := {(x, y)}) (by
            simpa [StatMech.Euc.regEdges] using he) (show a ∈ s(a, b) by simp)
          simpa [regVerts] using ha))
        (skeletonVertexOfCorner S (x, y) hc b (by
          have hb := wad_edge_mem_regVerts (K := {(x, y)}) (by
            simpa [StatMech.Euc.regEdges] using he) (show b ∈ s(a, b) by simp)
          simpa [regVerts] using hb)) := by
    change s(a, b) ∈ StatMech.Euc.regEdges S
    rw [StatMech.Euc.regEdges, Finset.mem_biUnion]
    exact ⟨(x, y), hc, he⟩
  have hbottom := hedge (x, y) (x + 1, y) (by simp [StatMech.Euc.cellEdges])
  have hleft := hedge (x, y) (x, y + 1) (by simp [StatMech.Euc.cellEdges])
  have hright := hedge (x + 1, y) (x + 1, y + 1) (by simp [StatMech.Euc.cellEdges])
  simp only [StatMech.Euc.cellVerts, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with hv | hv | hv | hv
  · subst v; exact Reachable.refl _
  · subst v; exact hbottom.reachable.symm
  · subst v; exact hleft.reachable.symm
  · subst v; exact hright.reachable.symm.trans hbottom.reachable.symm


theorem cell_representatives_reachable_of_adj (S : Finset Cell) (c d : Cell)
    (hc : c ∈ S) (hd : d ∈ S)
    (hadj : (hypercubicLattice 2).Adj (cellFace c) (cellFace d)) :
    (cellSkeleton S).Reachable
      (skeletonVertexOfCorner S c hc c (by
        obtain ⟨x, y⟩ := c; simp [StatMech.Euc.cellVerts]))
      (skeletonVertexOfCorner S d hd d (by
        obtain ⟨x, y⟩ := d; simp [StatMech.Euc.cellVerts])) := by
  let e := Sym2.map cellFace.symm (sharedPrimalEdge (cellFace c) (cellFace d))
  have hec : e ∈ StatMech.Euc.regEdges ({c} : Finset Cell) :=
    sharedPrimalEdge_mem_regEdges {c} c (by simp) (cellFace d) hadj
  have hed : e ∈ StatMech.Euc.regEdges ({d} : Finset Cell) := by
    have h := sharedPrimalEdge_mem_regEdges {d} d (by simp) (cellFace c) hadj.symm
    rw [← sharedPrimalEdge_comm_of_adj hadj] at h
    exact h
  generalize heq : e = edge at hec hed
  induction edge with
  | h a b =>
      have hac : a ∈ StatMech.Euc.cellVerts c := by
        have h := wad_edge_mem_regVerts (K := {c}) hec (show a ∈ s(a, b) by simp)
        simpa [regVerts] using h
      have had : a ∈ StatMech.Euc.cellVerts d := by
        have h := wad_edge_mem_regVerts (K := {d}) hed (show a ∈ s(a, b) by simp)
        simpa [regVerts] using h
      have hca := (corner_reachable_lowerLeft S c hc a hac).symm
      have hda := corner_reachable_lowerLeft S d hd a had
      exact hca.trans hda


end StatMech.Onsager.CellEulerFaithful
