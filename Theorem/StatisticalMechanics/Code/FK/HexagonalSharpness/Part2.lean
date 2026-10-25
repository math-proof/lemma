/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.FiniteGraphBoundaryDifferential
import Theorem.StatisticalMechanics.Code.OSSS.DecisionTreeReindex
import Theorem.StatisticalMechanics.Code.FK.TriHexCoarseGeometry.Part3
import Def.StatisticalMechanics.Code.FK.HexagonalSharpness.Part3
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS RevealmentConstruction LindebergTree DecisionTree

open StatMech.OSSS.FiniteGraphBoundaryDifferential

theorem hexagonalBoxEdgeLE_injective {n m : Nat} (h : n ≤ m) :
    Function.Injective (hexagonalBoxEdgeLE h) := by
  intro e f hef
  apply Subtype.ext
  have hv := congrArg Subtype.val hef
  change Sym2.map (hexagonalBoxVertInclLE h) e.1 =
    Sym2.map (hexagonalBoxVertInclLE h) f.1 at hv
  have hinj : Function.Injective (hexagonalBoxVertInclLE h) := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : HexagonalBoxVertex m => (z : HexVertex)) hxy
  exact (Sym2.map.injective hinj) hv

theorem hexagonal_adj_mem_box_succ
    {k : Nat} {x y : HexVertex} (hx : x.1 ∈ box 2 k)
    (hxy : hexagonalGraph.Adj x y) :
    y.1 ∈ box 2 (k + 1) := by
  rw [hexagonalGraph_adj] at hxy
  rcases hxy with ⟨_, _, i, h⟩ | ⟨_, _, i, h⟩
  · intro j
    have hj := hx j
    fin_cases i <;> fin_cases j <;>
      simp [hexagonalStep, funext_iff] at h hj ⊢ <;> omega
  · intro j
    have hj := hx j
    fin_cases i <;> fin_cases j <;>
      simp [hexagonalStep, funext_iff] at h hj ⊢ <;> omega

theorem hexagonal_adj_mem_box_of_mem_pred
    {k : Nat} (hk : 1 ≤ k) {x y : HexVertex}
    (hx : x.1 ∈ box 2 (k - 1)) (hxy : hexagonalGraph.Adj x y) :
    y.1 ∈ box 2 k := by
  simpa [Nat.sub_add_cancel hk] using hexagonal_adj_mem_box_succ hx hxy

theorem hexagonalBox_reachOpen_crosses
    {n k m : Nat} (hk : 1 ≤ k) (hkm : k ≤ m)
    (omega : ConfigSpace (hexagonalBoxGraph n).edgeSet)
    (h : ConnOpenSet (hexagonalBoxEndU n) (hexagonalBoxEndV n) omega
      (hexagonalBoxRoot n) (hexagonalBoxShell n m)) :
    ConnOpenSet (hexagonalBoxEndU n) (hexagonalBoxEndV n) omega
      (hexagonalBoxRoot n) (hexagonalBoxShell n k) := by
  obtain ⟨b, hb, hreach⟩ := h
  have hbOuter : b.1.1 ∉ box 2 (k - 1) := by
    have hbN := (Finset.mem_filter.mp hb).2.2
    intro hbk
    exact hbN (box_mono 2 (by omega) hbk)
  have hroot : (hexagonalBoxRoot n).1.1 ∈ box 2 (k - 1) := by
    intro j
    simp [hexagonalBoxRoot]
  have hfirst : ∀ {x b : HexagonalBoxVertex n},
      ReachOpen (hexagonalBoxEndU n) (hexagonalBoxEndV n) omega x b →
      x.1.1 ∈ box 2 (k - 1) → b.1.1 ∉ box 2 (k - 1) →
      ConnOpenSet (hexagonalBoxEndU n) (hexagonalBoxEndV n) omega x
        (hexagonalBoxShell n k) := by
    intro x b hr
    induction hr with
    | refl x => intro hx hnot; exact (hnot hx).elim
    | @step x y z e hopen hpair hrest ih =>
        intro hx hz
        have hxy : (hexagonalBoxGraph n).Adj x y := by
          rcases hpair with hpair | hpair
          · rw [← hpair.1, ← hpair.2]
            exact hexagonalBox_end_adj n e
          · rw [← hpair.1, ← hpair.2]
            exact (hexagonalBox_end_adj n e).symm
        by_cases hy : y.1.1 ∈ box 2 (k - 1)
        · obtain ⟨w, hw, hwy⟩ := ih hy hz
          exact ⟨w, hw, ReachOpen.step e hopen hpair hwy⟩
        · have hyk : y.1.1 ∈ box 2 k :=
            hexagonal_adj_mem_box_of_mem_pred hk hx hxy
          refine ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyk, hy⟩,
            ReachOpen.step e hopen hpair (ReachOpen.refl y)⟩
  exact hfirst hreach hroot hbOuter

theorem hexagonalBoxGraph_edgeSet_nonempty (n : Nat) (hn : 1 ≤ n) :
    Nonempty (hexagonalBoxGraph n).edgeSet := by
  let x : HexagonalBoxVertex n := hexagonalBoxRoot n
  let yFull := hexagonalNeighbor (hexagonalBoxEmbedding n x) 0
  let y : HexagonalBoxVertex n :=
    ⟨yFull, ⟨by
      intro j
      fin_cases j <;>
        simp [yFull, x, hexagonalBoxRoot, hexagonalBoxEmbedding,
          hexagonalNeighbor, hexagonalStep] <;> omega, Set.mem_univ _⟩⟩
  refine ⟨⟨s(x, y), ?_⟩⟩
  change hexagonalGraph.Adj (hexagonalBoxEmbedding n x)
    (hexagonalBoxEmbedding n y)
  simpa [y, yFull, hexagonalBoxEmbedding] using
    hexagonal_adj_neighbor (hexagonalBoxEmbedding n x) 0

end StatMech.FK.PeriodicPlanar
