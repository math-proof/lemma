/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanInteriorLib.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.OrbitExteriorEven
import Theorem.StatisticalMechanics.Code.Lattice.JordanLeftRegionInterior
import Theorem.StatisticalMechanics.Code.Lattice.FloodFillConnected.Part3
import Def.StatisticalMechanics.Code.Lattice.JordanInteriorLib.Part3
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem jil_stepGraph_walk_offSupport {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : jil_offSupportInterior Vc}
    (w : (jil_interiorStepGraph Vc).Walk x y) :
    ∃ p : (hypercubicLattice 2).Walk (x : Site 2) (y : Site 2), ∀ z ∈ p.support, z ∉ Vc.support := by
  classical
  induction w with
  | @nil u => exact ⟨SimpleGraph.Walk.nil, by
      intro z hz
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      subst hz
      exact (jil_mem_offSupportInterior Vc (u : Site 2) |>.mp u.2).1⟩
  | @cons u v t hadj q ih =>
    obtain ⟨p, hp⟩ := ih
    have hadj' : (hypercubicLattice 2).Adj (u : Site 2) (v : Site 2) := by
      rw [jil_interiorStepGraph] at hadj
      exact SimpleGraph.induce_adj.mp hadj
    have huoff : (u : Site 2) ∉ Vc.support :=
      (jil_mem_offSupportInterior Vc (u : Site 2) |>.mp u.2).1
    refine ⟨SimpleGraph.Walk.cons hadj' p, ?_⟩
    intro z hz
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with h | h
    · subst h; exact huoff
    · exact hp z h


theorem jil_rowLinked_of_stepReachable {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseedI : seed ∈ jil_offSupportInterior Vc)
    (hstep : ∀ z : jil_offSupportInterior Vc,
      (jil_interiorStepGraph Vc).Reachable z ⟨seed, hseedI⟩) :
    jil_RowLinked Vc seed := by
  intro z hz
  obtain ⟨w⟩ := hstep ⟨z, hz⟩
  exact jil_stepGraph_walk_offSupport Vc w


theorem jil_stepGraph_horizontal_adj {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : ℤ} (hu : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hv : (![x + 1, y] : Site 2) ∈ jil_offSupportInterior Vc) :
    (jil_interiorStepGraph Vc).Adj ⟨![x, y], hu⟩ ⟨![x + 1, y], hv⟩ := by
  rw [jil_interiorStepGraph, SimpleGraph.induce_adj]
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp


theorem jil_stepGraph_vertical_adj {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : ℤ} (hu : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hv : (![x, y + 1] : Site 2) ∈ jil_offSupportInterior Vc) :
    (jil_interiorStepGraph Vc).Adj ⟨![x, y], hu⟩ ⟨![x, y + 1], hv⟩ := by
  rw [jil_interiorStepGraph, SimpleGraph.induce_adj]
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp

end Lattice
end StatMech
