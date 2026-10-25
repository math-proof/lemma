/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ArcNoSeparation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Lattice.FiniteComplementConnected
import Theorem.StatisticalMechanics.Code.Lattice.FloodFillConnected.Part3
import Def.StatisticalMechanics.Code.Lattice.ArcNoSeparation.Part4
open Set SimpleGraph


namespace StatMech

namespace Lattice

theorem arcns_connected_insert_of_leafRemovable {S : Set (Site 2)} {u' : Site 2}
    (hres : arcns_LeafRemovable S u') (hS : arcns_OffSupportConnected S) :
    arcns_OffSupportConnected (insert u' S) :=
  hres hS


theorem arcns_cons_support {u v w : Site 2} (h : (hypercubicLattice 2).Adj u v)
    (q : (hypercubicLattice 2).Walk v w) :
    {z : Site 2 | z ∈ (Walk.cons h q).support}
      = insert u {z : Site 2 | z ∈ q.support} := by
  ext z
  simp only [Walk.support_cons, List.mem_cons, Set.mem_setOf_eq, Set.mem_insert_iff]


theorem arcns_arc_no_separation {u w : Site 2} (p : (hypercubicLattice 2).Walk u w)
    (hp : p.IsPath)
    (hleaf : ∀ (a b c : Site 2) (h : (hypercubicLattice 2).Adj a b)
      (q : (hypercubicLattice 2).Walk b c), (Walk.cons h q).IsPath →
        arcns_LeafRemovable {z : Site 2 | z ∈ q.support} a) :
    arcns_OffSupportConnected {z : Site 2 | z ∈ p.support} := by
  induction p with
  | nil =>
    
    rename_i v
    have hsupp : {z : Site 2 | z ∈ (Walk.nil : (hypercubicLattice 2).Walk v v).support}
        = ({v} : Set (Site 2)) := by
      ext z; simp [Walk.support_nil]
    rw [hsupp]; exact arcns_singlePoint_connected v
  | @cons a b c h q ih =>
    have hpath : (Walk.cons h q).IsPath := hp
    have hqpath : q.IsPath := hpath.of_cons
    have hIH : arcns_OffSupportConnected {z : Site 2 | z ∈ q.support} := ih hqpath
    rw [arcns_cons_support]
    exact arcns_connected_insert_of_leafRemovable (hleaf a b c h q hpath) hIH


theorem arcns_offSupport_reachable_of_arc {u w : Site 2} (p : (hypercubicLattice 2).Walk u w)
    (hp : p.IsPath)
    (hleaf : ∀ (a b c : Site 2) (h : (hypercubicLattice 2).Adj a b)
      (q : (hypercubicLattice 2).Walk b c), (Walk.cons h q).IsPath →
        arcns_LeafRemovable {z : Site 2 | z ∈ q.support} a)
    {x y : Site 2} (hx : x ∉ {z : Site 2 | z ∈ p.support})
    (hy : y ∉ {z : Site 2 | z ∈ p.support}) :
    (ffc_offSupportLattice {z : Site 2 | z ∈ p.support}).Reachable x y :=
  arcns_arc_no_separation p hp hleaf x y hx hy


theorem arcns_floodFill_eq_offSupport_of_arc {u w : Site 2}
    (p : (hypercubicLattice 2).Walk u w) (hp : p.IsPath)
    (hleaf : ∀ (a b c : Site 2) (h : (hypercubicLattice 2).Adj a b)
      (q : (hypercubicLattice 2).Walk b c), (Walk.cons h q).IsPath →
        arcns_LeafRemovable {z : Site 2 | z ∈ q.support} a)
    {seed : Site 2} (hseed : seed ∉ {z : Site 2 | z ∈ p.support}) :
    ffc_floodFill {z : Site 2 | z ∈ p.support} seed
      = {z : Site 2 | z ∉ {z : Site 2 | z ∈ p.support}} := by
  ext z
  constructor
  · intro hz
    exact ffc_floodFill_offSupport hseed hz
  · intro hz
    rw [Set.mem_setOf_eq] at hz
    rw [ffc_mem_floodFill]
    exact arcns_arc_no_separation p hp hleaf seed z hseed hz


theorem arcns_singlePoint_nonvacuous :
    (ffc_offSupportLattice ({![0, 0]} : Set (Site 2))).Reachable ![1, 0] ![0, 1] := by
  apply arcns_singlePoint_connected
  · simp only [Set.mem_singleton_iff]; intro h; have := congrFun h 0; simp at this
  · simp only [Set.mem_singleton_iff]; intro h; have := congrFun h 1; simp at this


theorem arcns_leafRemovable_empty (u : Site 2) :
    arcns_LeafRemovable (∅ : Set (Site 2)) u := by
  intro _
  have hins : (insert u (∅ : Set (Site 2))) = ({u} : Set (Site 2)) := by simp
  rw [hins]; exact arcns_singlePoint_connected u


end Lattice
end StatMech
