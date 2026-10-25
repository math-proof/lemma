/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourAnchor.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EnclosingLength.Part2
import Def.StatisticalMechanics.Code.Lattice.LeftFace.Part4
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem leftExitFaceUp_coord0_nonpos (hfin : (cluster 2 ω (origin 2)).Finite) :
    leftExitFaceUp (ω := ω) hfin 0 ≤ 0 := by
  show -(leftExitIndex (ω := ω) hfin : ℤ) - 1 ≤ 0
  have : (0 : ℤ) ≤ (leftExitIndex (ω := ω) hfin : ℤ) := Int.natCast_nonneg _
  omega

theorem leftExitFaceDown_coord0_nonpos (hfin : (cluster 2 ω (origin 2)).Finite) :
    leftExitFaceDown (ω := ω) hfin 0 ≤ 0 := by
  show -(leftExitIndex (ω := ω) hfin : ℤ) - 1 ≤ 0
  have : (0 : ℤ) ≤ (leftExitIndex (ω := ω) hfin : ℤ) := Int.natCast_nonneg _
  omega


theorem sharedPrimalEdge_leftExitFaces (hfin : (cluster 2 ω (origin 2)).Finite) :
    sharedPrimalEdge (leftExitFaceUp (ω := ω) hfin) (leftExitFaceDown (ω := ω) hfin)
      = s(leftAxisSite (leftExitIndex (ω := ω) hfin),
          leftAxisSite (leftExitIndex (ω := ω) hfin + 1)) := by
  have hup : (leftExitFaceUp (ω := ω) hfin : Site 2)
      = ![-(leftExitIndex (ω := ω) hfin : ℤ) - 1, 0] := rfl
  have hdown : (leftExitFaceDown (ω := ω) hfin : Site 2)
      = ![-(leftExitIndex (ω := ω) hfin : ℤ) - 1, (0 : ℤ) - 1] := by
    unfold leftExitFaceDown; funext i; fin_cases i <;> simp
  have hax0 : (leftAxisSite (leftExitIndex (ω := ω) hfin) : Site 2)
      = ![-(leftExitIndex (ω := ω) hfin : ℤ), 0] := rfl
  have hax1 : (leftAxisSite (leftExitIndex (ω := ω) hfin + 1) : Site 2)
      = ![-(leftExitIndex (ω := ω) hfin : ℤ) - 1, 0] := leftAxisSite_succ_eq _
  rw [hup, hdown, sharedPrimalEdge_bottom (-(leftExitIndex (ω := ω) hfin : ℤ) - 1) 0,
    hax0, hax1]
  unfold faceCorner00 faceCorner10
  
  rw [Sym2.eq_swap]
  have hsimp : -(leftExitIndex (ω := ω) hfin : ℤ) - 1 + 1
      = -(leftExitIndex (ω := ω) hfin : ℤ) := by ring
  rw [hsimp]


theorem leftExitFaces_adj (hfin : (cluster 2 ω (origin 2)).Finite) :
    (hypercubicLattice 2).Adj (leftExitFaceUp (ω := ω) hfin)
      (leftExitFaceDown (ω := ω) hfin) := by
  have hup : (leftExitFaceUp (ω := ω) hfin : Site 2)
      = ![-(leftExitIndex (ω := ω) hfin : ℤ) - 1, 0] := rfl
  have hdown : (leftExitFaceDown (ω := ω) hfin : Site 2)
      = ![-(leftExitIndex (ω := ω) hfin : ℤ) - 1, (0 : ℤ) - 1] := by
    unfold leftExitFaceDown; funext i; fin_cases i <;> simp
  rw [hup, hdown]
  exact latAdj_bottom (-(leftExitIndex (ω := ω) hfin : ℤ) - 1) 0


theorem leftExitFaces_faceBoundaryGraph_adj (hfin : (cluster 2 ω (origin 2)).Finite) :
    (faceBoundaryGraph (cluster 2 ω (origin 2))).Adj
      (leftExitFaceUp (ω := ω) hfin) (leftExitFaceDown (ω := ω) hfin) := by
  rw [faceBoundaryGraph_adj]
  refine ⟨leftExitFaces_adj (ω := ω) hfin, ?_⟩
  rw [sharedPrimalEdge_leftExitFaces (ω := ω) hfin, bdEdge_mk]
  refine ⟨fun _ => leftAxisSite_exit_succ_not_mem (ω := ω) hfin, fun _ => ?_⟩
  exact leftAxisSite_exit_mem (ω := ω) hfin


theorem exists_faceBoundaryGraph_leftEdge (hfin : (cluster 2 ω (origin 2)).Finite) :
    ∃ f g : Site 2, (faceBoundaryGraph (cluster 2 ω (origin 2))).Adj f g ∧
      f 0 ≤ 0 ∧ g 0 ≤ 0 :=
  ⟨leftExitFaceUp (ω := ω) hfin, leftExitFaceDown (ω := ω) hfin,
    leftExitFaces_faceBoundaryGraph_adj (ω := ω) hfin,
    leftExitFaceUp_coord0_nonpos (ω := ω) hfin,
    leftExitFaceDown_coord0_nonpos (ω := ω) hfin⟩


theorem exists_cycle_through_leftEdge (hfin : (cluster 2 ω (origin 2)).Finite) :
    ∃ (u : Site 2) (c : (faceBoundaryGraph (cluster 2 ω (origin 2))).Walk u u),
      c.IsCycle ∧
        s(leftExitFaceUp (ω := ω) hfin, leftExitFaceDown (ω := ω) hfin) ∈ c.edges := by
  obtain ⟨T, hT⟩ :=
    exists_finset_support_faceBoundaryGraph (cluster 2 ω (origin 2)) hfin
  exact EvenDegree.exists_cycle_through_edge_of_even_of_finite_support
    (faceBoundaryGraph (cluster 2 ω (origin 2))) T hT
    (degree_faceBoundaryGraph_even (cluster 2 ω (origin 2)))
    (leftExitFaces_faceBoundaryGraph_adj (ω := ω) hfin)


theorem cycleHasLeftFace_of_cycle_through_exitFaceUp_and_leftFace
    (hfin : (cluster 2 ω (origin 2)).Finite)
    (h : ∃ (u : Site 2) (c : (faceBoundaryGraph (cluster 2 ω (origin 2))).Walk u u),
        c.IsCycle ∧ exitFaceUp (ω := ω) hfin ∈ c.support ∧ ∃ w ∈ c.support, w 0 ≤ 0) :
    CycleHasLeftFace ω hfin := by
  classical
  obtain ⟨u, c, hcyc, hup, w, hwsup, hw0⟩ := h
  
  refine ⟨c.rotate (exitFaceUp (ω := ω) hfin) hup, hcyc.rotate hup, w, ?_, hw0⟩
  
  rw [SimpleGraph.Walk.mem_support_rotate_iff]
  exact hwsup


theorem cycleHasLeftFace_of_exitFaceUp_cycle_through_leftEdge
    (hfin : (cluster 2 ω (origin 2)).Finite)
    (c : (faceBoundaryGraph (cluster 2 ω (origin 2))).Walk
        (exitFaceUp (ω := ω) hfin) (exitFaceUp (ω := ω) hfin))
    (hcyc : c.IsCycle)
    (hedge : s(leftExitFaceUp (ω := ω) hfin, leftExitFaceDown (ω := ω) hfin) ∈ c.edges) :
    CycleHasLeftFace ω hfin := by
  
  
  refine ⟨c, hcyc, leftExitFaceUp (ω := ω) hfin, c.fst_mem_support_of_mem_edges hedge,
    leftExitFaceUp_coord0_nonpos (ω := ω) hfin⟩


theorem anchoredCycleExists_of_exitFaceUp_cycle_through_leftEdge
    (hfin : (cluster 2 ω (origin 2)).Finite)
    (c : (faceBoundaryGraph (cluster 2 ω (origin 2))).Walk
        (exitFaceUp (ω := ω) hfin) (exitFaceUp (ω := ω) hfin))
    (hcyc : c.IsCycle)
    (hedge : s(leftExitFaceUp (ω := ω) hfin, leftExitFaceDown (ω := ω) hfin) ∈ c.edges) :
    AnchoredCycleExists ω hfin :=
  anchoredCycleExists_of_leftFace (ω := ω) hfin
    (cycleHasLeftFace_of_exitFaceUp_cycle_through_leftEdge (ω := ω) hfin c hcyc hedge)


theorem pcAnchoredEnclosure_of_exitFaceUp_cycle_through_leftEdge
    (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        ∃ c : (faceBoundaryGraph (cluster 2 ω (origin 2))).Walk
            (exitFaceUp (ω := ω) hfin) (exitFaceUp (ω := ω) hfin),
          c.IsCycle ∧
            s(leftExitFaceUp (ω := ω) hfin, leftExitFaceDown (ω := ω) hfin) ∈ c.edges) :
    StatMech.Percolation.PcAnchoredEnclosure := by
  refine pcAnchoredEnclosure_of_cycleHasLeftFace (fun ω hfin => ?_)
  obtain ⟨c, hcyc, hedge⟩ := h ω hfin
  exact cycleHasLeftFace_of_exitFaceUp_cycle_through_leftEdge (ω := ω) hfin c hcyc hedge


end Lattice
end StatMech
