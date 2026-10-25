/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCoresUnify.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ArcSides.Part3
import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.OrbitEncloses.Part4
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

open StatMech.RSW.Box

open StatMech.Universality


theorem jcu_walk_crosses (S : Set (Site 2)) {x y : Site 2} (hx : x ∈ S) (hy : y ∉ S)
    (w : (hypercubicLattice 2).Walk x y) :
    ∃ e ∈ w.edges, bdEdge S e := by
  classical
  by_contra hcon
  push Not at hcon
  have h0 : crossCount S w = 0 := by
    rw [crossCount, List.countP_eq_zero]
    exact fun e he => by simp only [decide_eq_true_eq]; exact hcon e he
  exact (crossCount_odd_of_separated S hx hy w) (h0 ▸ Even.zero)


theorem jcu_walk_meets_innerBoundary (S : Set (Site 2)) {x y : Site 2} (hx : x ∈ S) (hy : y ∉ S)
    (w : (hypercubicLattice 2).Walk x y) :
    ∃ u v : Site 2, u ∈ w.support ∧ v ∈ w.support ∧
      (hypercubicLattice 2).Adj u v ∧ u ∈ S ∧ v ∉ S := by
  classical
  obtain ⟨e, hew, hbd⟩ := jcu_walk_crosses S hx hy w
  
  induction e with | _ a b =>
  have hadj : (hypercubicLattice 2).Adj a b := w.adj_of_mem_edges hew
  rw [bdEdge_mk] at hbd
  have ha : a ∈ w.support := w.fst_mem_support_of_mem_edges hew
  have hb : b ∈ w.support := w.snd_mem_support_of_mem_edges hew
  by_cases haS : a ∈ S
  · exact ⟨a, b, ha, hb, hadj, haS, hbd.mp haS⟩
  · 
    have hbS : b ∈ S := by by_contra hbS; exact haS (by tauto)
    exact ⟨b, a, hb, ha, hadj.symm, hbS, fun haS' => (hbd.mp haS') hbS⟩


end Lattice
end StatMech
