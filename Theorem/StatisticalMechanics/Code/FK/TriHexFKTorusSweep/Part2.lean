/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKGlobalSweep.Part5
import Theorem.StatisticalMechanics.Code.FK.TriHexTorusDuality.Part10
import Theorem.StatisticalMechanics.Code.FK.ActiveEdges.Part4
import Theorem.StatisticalMechanics.Code.Universality.STTTransport.Part3
import Def.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part2


namespace StatMech.FK.PeriodicPlanar

open Universality

open scoped BigOperators


@[simp] theorem triangularTorusActiveConfigEquiv_apply
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (triangularTorusGraph L).edgeSet)
    (z : TorusSite L) :
    triangularTorusActiveConfigEquiv L omega z =
      (omega (triHexTorusTriangleSweepEdgeEquiv L (z, 0)),
        omega (triHexTorusTriangleSweepEdgeEquiv L (z, 1)),
        omega (triHexTorusTriangleSweepEdgeEquiv L (z, 2))) := rfl

@[simp] theorem triangularTorusActiveConfigEquiv_direction
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (triangularTorusGraph L).edgeSet)
    (z : TorusSite L) (i : Fin 3) :
    triHexLocalDirection (triangularTorusActiveConfigEquiv L omega z) i =
      omega (triHexTorusTriangleSweepEdgeEquiv L (z, i)) := by
  fin_cases i <;> rfl

@[simp] theorem hexagonalTorusActiveConfigEquiv_apply
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet)
    (z : TorusSite L) :
    hexagonalTorusActiveConfigEquiv L omega z =
      (omega (triHexTorusStarSweepEdgeEquiv L (z, 0)),
        omega (triHexTorusStarSweepEdgeEquiv L (z, 1)),
        omega (triHexTorusStarSweepEdgeEquiv L (z, 2))) := rfl

@[simp] theorem hexagonalTorusActiveConfigEquiv_direction
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet)
    (z : TorusSite L) (i : Fin 3) :
    triHexLocalDirection (hexagonalTorusActiveConfigEquiv L omega z) i =
      omega (triHexTorusStarSweepEdgeEquiv L (z, i)) := by
  fin_cases i <;> rfl


theorem triangularTorus_openSub_adj_cellEdge
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (triangularTorusGraph L).edgeSet)
    (z : TorusSite L) (i : Fin 3)
    (hopen : triHexLocalDirection
      (triangularTorusActiveConfigEquiv L omega z) i = true) :
    (openSub (triangularTorusGraph L)
      (extendActive (triangularTorusGraph L) omega)).Adj
        (triHexTorusCellTerminal L z (triHexTriangleEdgeTerminal1 i))
        (triHexTorusCellTerminal L z (triHexTriangleEdgeTerminal2 i)) := by
  rw [openSub_adj]
  let e := triHexTorusTriangleSweepEdgeEquiv L (z, i)
  have heq : (e.1 : Sym2 (TorusSite L)) =
      s(triHexTorusCellTerminal L z (triHexTriangleEdgeTerminal1 i),
        triHexTorusCellTerminal L z (triHexTriangleEdgeTerminal2 i)) :=
    triHexTorusTriangleSweepEdge_val L z i
  constructor
  · rw [← SimpleGraph.mem_edgeSet, ← heq]
    exact e.2
  · rw [← heq, extendActive_apply]
    fin_cases i <;> exact hopen


theorem hexagonalTorus_openSub_adj_spoke
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet)
    (z : TorusSite L) (i : Fin 3)
    (hopen : triHexLocalDirection
      (hexagonalTorusActiveConfigEquiv L omega z) i = true) :
    (openSub (hexagonalTorusGraph L)
      (extendActive (hexagonalTorusGraph L) omega)).Adj
        (z, false) (triHexTorusCellTerminal L z i, true) := by
  rw [openSub_adj]
  let e := triHexTorusStarSweepEdgeEquiv L (z, i)
  have heq : (e.1 : Sym2 (HexTorusVertex L)) =
      s((z, false), (triHexTorusCellTerminal L z i, true)) :=
    triHexTorusStarSweepEdge_val L z i
  constructor
  · rw [← SimpleGraph.mem_edgeSet, ← heq]
    exact e.2
  · rw [← heq, extendActive_apply]
    change omega (triHexTorusStarSweepEdgeEquiv L (z, i)) = true
    exact (hexagonalTorusActiveConfigEquiv_direction L omega z i).symm.trans hopen


theorem hexagonalTorus_openSub_adj_center_iff
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet)
    (z : TorusSite L) (v : HexTorusVertex L) :
    (openSub (hexagonalTorusGraph L)
      (extendActive (hexagonalTorusGraph L) omega)).Adj (z, false) v ↔
      ∃ i : Fin 3,
        triHexLocalDirection (hexagonalTorusActiveConfigEquiv L omega z) i = true ∧
          v = (triHexTorusCellTerminal L z i, true) := by
  constructor
  · intro h
    obtain ⟨⟨a, i⟩, ha⟩ := h.1
    rw [hexagonalTorusIndexedEdge, Sym2.eq_iff] at ha
    rcases ha with ⟨hcenter, hterminal⟩ | ⟨hbad, _hbad'⟩
    · have haz : a = z := congrArg Prod.fst hcenter
      subst a
      refine ⟨i, ?_, hterminal.symm⟩
      rw [hexagonalTorusActiveConfigEquiv_direction]
      let e := triHexTorusStarSweepEdgeEquiv L (z, i)
      have heq : (e.1 : Sym2 (HexTorusVertex L)) = s((z, false), v) := by
        rw [triHexTorusStarSweepEdge_val]
        exact congrArg (fun w => s((z, false), w)) hterminal
      have hopen := h.2
      rw [← heq, extendActive_apply] at hopen
      exact hopen
    · have : (true : Bool) = false := by
        exact congrArg Prod.snd _hbad'
      simp at this
  · rintro ⟨i, hopen, rfl⟩
    exact hexagonalTorus_openSub_adj_spoke L omega z i hopen


theorem triangleFKLocalConnectivity_connects_zero_one
    (config : LocalConfig) :
    (triangleFKLocalConnectivity config).Connects 0 1 ↔
      triHexLocalDirection config 2 = true ∨
        (triHexLocalDirection config 0 = true ∧
          triHexLocalDirection config 1 = true) := by
  rcases config with ⟨b0, b1, b2⟩
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;>
    simp [triangleFKLocalConnectivity, ThreeTerminalConnectivity.Connects,
      triHexLocalDirection]


theorem triangleFKLocalConnectivity_connects_zero_two
    (config : LocalConfig) :
    (triangleFKLocalConnectivity config).Connects 0 2 ↔
      triHexLocalDirection config 1 = true ∨
        (triHexLocalDirection config 0 = true ∧
          triHexLocalDirection config 2 = true) := by
  rcases config with ⟨b0, b1, b2⟩
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;>
    simp [triangleFKLocalConnectivity, ThreeTerminalConnectivity.Connects,
      triHexLocalDirection]


theorem triangleFKLocalConnectivity_connects_one_two
    (config : LocalConfig) :
    (triangleFKLocalConnectivity config).Connects 1 2 ↔
      triHexLocalDirection config 0 = true ∨
        (triHexLocalDirection config 1 = true ∧
          triHexLocalDirection config 2 = true) := by
  rcases config with ⟨b0, b1, b2⟩
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;>
    simp [triangleFKLocalConnectivity, ThreeTerminalConnectivity.Connects,
      triHexLocalDirection]


theorem triangularTorus_openSub_reachable_of_connects
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (triangularTorusGraph L).edgeSet)
    (z : TorusSite L) (i j : Fin 3)
    (hconnects : (triangleFKLocalConnectivity
      (triangularTorusActiveConfigEquiv L omega z)).Connects i j) :
    (openSub (triangularTorusGraph L)
      (extendActive (triangularTorusGraph L) omega)).Reachable
        (triHexTorusCellTerminal L z i)
        (triHexTorusCellTerminal L z j) := by
  let config := triangularTorusActiveConfigEquiv L omega z
  let edgeReach (k : Fin 3)
      (h : triHexLocalDirection config k = true) :=
    SimpleGraph.Adj.reachable
      (triangularTorus_openSub_adj_cellEdge L omega z k h)
  have reach01 (h : (triangleFKLocalConnectivity config).Connects 0 1) :
      (openSub (triangularTorusGraph L)
        (extendActive (triangularTorusGraph L) omega)).Reachable
          (triHexTorusCellTerminal L z 0) (triHexTorusCellTerminal L z 1) := by
    rcases (triangleFKLocalConnectivity_connects_zero_one config).mp h with
      h2 | ⟨h0, h1⟩
    · exact edgeReach 2 h2
    · exact (edgeReach 1 h1).symm.trans (edgeReach 0 h0).symm
  have reach02 (h : (triangleFKLocalConnectivity config).Connects 0 2) :
      (openSub (triangularTorusGraph L)
        (extendActive (triangularTorusGraph L) omega)).Reachable
          (triHexTorusCellTerminal L z 0) (triHexTorusCellTerminal L z 2) := by
    rcases (triangleFKLocalConnectivity_connects_zero_two config).mp h with
      h1 | ⟨h0, h2⟩
    · exact (edgeReach 1 h1).symm
    · exact (edgeReach 2 h2).trans (edgeReach 0 h0)
  have reach12 (h : (triangleFKLocalConnectivity config).Connects 1 2) :
      (openSub (triangularTorusGraph L)
        (extendActive (triangularTorusGraph L) omega)).Reachable
          (triHexTorusCellTerminal L z 1) (triHexTorusCellTerminal L z 2) := by
    rcases (triangleFKLocalConnectivity_connects_one_two config).mp h with
      h0 | ⟨h1, h2⟩
    · exact edgeReach 0 h0
    · exact (edgeReach 2 h2).symm.trans (edgeReach 1 h1).symm
  fin_cases i <;> fin_cases j
  · exact SimpleGraph.Reachable.refl _
  · exact reach01 hconnects
  · exact reach02 hconnects
  · exact (reach01
      ((triangleFKLocalConnectivity config).connects_symm 0 1 |>.mpr hconnects)).symm
  · exact SimpleGraph.Reachable.refl _
  · exact reach12 hconnects
  · exact (reach02
      ((triangleFKLocalConnectivity config).connects_symm 0 2 |>.mpr hconnects)).symm
  · exact (reach12
      ((triangleFKLocalConnectivity config).connects_symm 1 2 |>.mpr hconnects)).symm
  · exact SimpleGraph.Reachable.refl _


end StatMech.FK.PeriodicPlanar
