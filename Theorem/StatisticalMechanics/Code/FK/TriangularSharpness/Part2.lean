/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.FiniteGraphBoundaryDifferential
import Theorem.StatisticalMechanics.Code.OSSS.DecisionTreeReindex
import Theorem.StatisticalMechanics.Code.FK.TriHexCoarseGeometry.Part3
import Def.StatisticalMechanics.Code.FK.TriangularSharpness.Part3
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS RevealmentConstruction LindebergTree DecisionTree

open StatMech.OSSS.FiniteGraphBoundaryDifferential

theorem triangularBoxEdgeLE_injective {n m : Nat} (h : n ≤ m) :
    Function.Injective (triangularBoxEdgeLE h) := by
  intro e f hef
  apply Subtype.ext
  have hv := congrArg Subtype.val hef
  change innerEdgeLE 2 h e.1 = innerEdgeLE 2 h f.1 at hv
  have hinj : Function.Injective (boxVertInclLE 2 h) := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : boxVerts 2 m => (z : Site 2)) hxy
  exact (Sym2.map.injective hinj) hv

theorem triangular_adj_mem_box_succ
    {k : Nat} {x y : Site 2} (hx : x ∈ box 2 k)
    (hxy : triangularGraph.Adj x y) :
    y ∈ box 2 (k + 1) := by
  rw [triangularGraph_adj] at hxy
  obtain ⟨i, h | h⟩ := hxy
  · intro j
    have hj := hx j
    fin_cases i <;> fin_cases j <;>
      simp [triangularStep, funext_iff] at h hj ⊢ <;> omega
  · intro j
    have hj := hx j
    fin_cases i <;> fin_cases j <;>
      simp [triangularStep, funext_iff] at h hj ⊢ <;> omega

theorem triangular_adj_mem_box_of_mem_pred
    {k : Nat} (hk : 1 ≤ k) {x y : Site 2}
    (hx : x ∈ box 2 (k - 1)) (hxy : triangularGraph.Adj x y) :
    y ∈ box 2 k := by
  simpa [Nat.sub_add_cancel hk] using triangular_adj_mem_box_succ hx hxy

theorem triangularBox_reachOpen_crosses
    {n k m : Nat} (hk : 1 ≤ k) (hkm : k ≤ m)
    (omega : ConfigSpace (triangularBoxGraph n).edgeSet)
    (h : ConnOpenSet (triangularBoxEndU n) (triangularBoxEndV n) omega
      (triangularBoxRoot n) (triangularBoxShell n m)) :
    ConnOpenSet (triangularBoxEndU n) (triangularBoxEndV n) omega
      (triangularBoxRoot n) (triangularBoxShell n k) := by
  obtain ⟨b, hb, hreach⟩ := h
  have hbOuter : b.1 ∉ box 2 (k - 1) := by
    have hbN := (Finset.mem_filter.mp hb).2.2
    intro hbk
    exact hbN (box_mono 2 (by omega) hbk)
  have hroot : (triangularBoxRoot n).1 ∈ box 2 (k - 1) := by
    intro j
    simp [triangularBoxRoot]
  have hfirst : ∀ {x b : TriangularBoxVertex n},
      ReachOpen (triangularBoxEndU n) (triangularBoxEndV n) omega x b →
      x.1 ∈ box 2 (k - 1) → b.1 ∉ box 2 (k - 1) →
      ConnOpenSet (triangularBoxEndU n) (triangularBoxEndV n) omega x
        (triangularBoxShell n k) := by
    intro x b hr
    induction hr with
    | refl x => intro hx hnot; exact (hnot hx).elim
    | @step x y z e hopen hpair hrest ih =>
        intro hx hz
        have hxy : (triangularBoxGraph n).Adj x y := by
          rcases hpair with hpair | hpair
          · rw [← hpair.1, ← hpair.2]
            exact triangularBox_end_adj n e
          · rw [← hpair.1, ← hpair.2]
            exact (triangularBox_end_adj n e).symm
        by_cases hy : y.1 ∈ box 2 (k - 1)
        · obtain ⟨w, hw, hwy⟩ := ih hy hz
          exact ⟨w, hw, ReachOpen.step e hopen hpair hwy⟩
        · have hyk : y.1 ∈ box 2 k :=
            triangular_adj_mem_box_of_mem_pred hk hx hxy
          refine ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyk, hy⟩,
            ReachOpen.step e hopen hpair (ReachOpen.refl y)⟩
  exact hfirst hreach hroot hbOuter

theorem triangularBoxGraph_edgeSet_nonempty (n : Nat) (hn : 1 ≤ n) :
    Nonempty (triangularBoxGraph n).edgeSet := by
  let x : TriangularBoxVertex n := triangularBoxRoot n
  let y : TriangularBoxVertex n := ⟨triangularNeighbor x.1 (0, true), by
    intro j
    fin_cases j <;>
      simp [x, triangularBoxRoot, triangularNeighbor, triangularStep] <;> omega⟩
  refine ⟨⟨s(x, y), ?_⟩⟩
  change triangularGraph.Adj x.1 y.1
  exact triangular_adj_neighbor x.1 (0, true)

end StatMech.FK.PeriodicPlanar
