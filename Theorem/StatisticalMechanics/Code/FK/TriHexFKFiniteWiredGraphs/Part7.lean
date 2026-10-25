/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredSweep.Part3
import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part15
import Def.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredGraphs.Part8
open Finset Set


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open Universality

noncomputable section

@[simp] theorem triHexPlanarFiniteTriangleConfigEquiv_direction
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteTriangleGraph n).edgeSet)
    (z : TriHexPlanarFiniteCell n) (i : Fin 3) :
    triHexLocalDirection (triHexPlanarFiniteTriangleConfigEquiv n omega z) i =
      omega (triHexPlanarFiniteTriangleEdgeEquiv n (z, i)) := by
  fin_cases i <;> rfl

@[simp] theorem triHexPlanarFiniteStarConfigEquiv_direction
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet)
    (z : TriHexPlanarFiniteCell n) (i : Fin 3) :
    triHexLocalDirection (triHexPlanarFiniteStarConfigEquiv n omega z) i =
      omega (triHexPlanarFiniteStarEdgeEquiv n (z, i)) := by
  fin_cases i <;> rfl


theorem triHexPlanarFiniteTriangle_openSub_adj_cellEdge
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteTriangleGraph n).edgeSet)
    (z : TriHexPlanarFiniteCell n) (i : Fin 3)
    (hopen : triHexLocalDirection
      (triHexPlanarFiniteTriangleConfigEquiv n omega z) i = true) :
    (openSub (triHexPlanarFiniteTriangleGraph n)
      (extendActive (triHexPlanarFiniteTriangleGraph n) omega)).Adj
        (triHexPlanarFiniteTerminalMap n z (triHexTriangleEdgeTerminal1 i))
        (triHexPlanarFiniteTerminalMap n z
          (triHexTriangleEdgeTerminal2 i)) := by
  rw [openSub_adj]
  constructor
  · rw [← SimpleGraph.mem_edgeSet]
    exact (triHexPlanarFiniteTriangleEdgeEquiv n (z, i)).2
  · change (extendActive (triHexPlanarFiniteTriangleGraph n) omega)
      (triHexPlanarFiniteTriangleEdge n (z, i)) = true
    rw [show triHexPlanarFiniteTriangleEdge n (z, i) =
        (triHexPlanarFiniteTriangleEdgeEquiv n (z, i)).1 from rfl,
      extendActive_apply]
    exact (triHexPlanarFiniteTriangleConfigEquiv_direction n omega z i).symm.trans
      hopen


theorem triHexPlanarFiniteTriangle_openSub_reachable_of_connects
    (n : Nat)
    (omega : ConfigSpace (triHexPlanarFiniteTriangleGraph n).edgeSet)
    (z : TriHexPlanarFiniteCell n) (i j : Fin 3)
    (hconnects : (triangleFKLocalConnectivity
      (triHexPlanarFiniteTriangleConfigEquiv n omega z)).Connects i j) :
    (openSub (triHexPlanarFiniteTriangleGraph n)
      (extendActive (triHexPlanarFiniteTriangleGraph n) omega)).Reachable
        (triHexPlanarFiniteTerminalMap n z i)
        (triHexPlanarFiniteTerminalMap n z j) := by
  let config := triHexPlanarFiniteTriangleConfigEquiv n omega z
  let edgeReach (k : Fin 3)
      (h : triHexLocalDirection config k = true) :=
    SimpleGraph.Adj.reachable
      (triHexPlanarFiniteTriangle_openSub_adj_cellEdge n omega z k h)
  have reach01 (h : (triangleFKLocalConnectivity config).Connects 0 1) :
      (openSub (triHexPlanarFiniteTriangleGraph n)
        (extendActive (triHexPlanarFiniteTriangleGraph n) omega)).Reachable
          (triHexPlanarFiniteTerminalMap n z 0)
          (triHexPlanarFiniteTerminalMap n z 1) := by
    rcases (triangleFKLocalConnectivity_connects_zero_one config).mp h with
      h2 | ⟨h0, h1⟩
    · exact edgeReach 2 h2
    · exact (edgeReach 1 h1).symm.trans (edgeReach 0 h0).symm
  have reach02 (h : (triangleFKLocalConnectivity config).Connects 0 2) :
      (openSub (triHexPlanarFiniteTriangleGraph n)
        (extendActive (triHexPlanarFiniteTriangleGraph n) omega)).Reachable
          (triHexPlanarFiniteTerminalMap n z 0)
          (triHexPlanarFiniteTerminalMap n z 2) := by
    rcases (triangleFKLocalConnectivity_connects_zero_two config).mp h with
      h1 | ⟨h0, h2⟩
    · exact (edgeReach 1 h1).symm
    · exact (edgeReach 2 h2).trans (edgeReach 0 h0)
  have reach12 (h : (triangleFKLocalConnectivity config).Connects 1 2) :
      (openSub (triHexPlanarFiniteTriangleGraph n)
        (extendActive (triHexPlanarFiniteTriangleGraph n) omega)).Reachable
          (triHexPlanarFiniteTerminalMap n z 1)
          (triHexPlanarFiniteTerminalMap n z 2) := by
    rcases (triangleFKLocalConnectivity_connects_one_two config).mp h with
      h0 | ⟨h1, h2⟩
    · exact edgeReach 0 h0
    · exact (edgeReach 2 h2).symm.trans (edgeReach 1 h1).symm
  fin_cases i <;> fin_cases j
  · exact SimpleGraph.Reachable.refl _
  · exact reach01 hconnects
  · exact reach02 hconnects
  · exact (reach01
      ((triangleFKLocalConnectivity config).connects_symm 0 1 |>.mpr
        hconnects)).symm
  · exact SimpleGraph.Reachable.refl _
  · exact reach12 hconnects
  · exact (reach02
      ((triangleFKLocalConnectivity config).connects_symm 0 2 |>.mpr
        hconnects)).symm
  · exact (reach12
      ((triangleFKLocalConnectivity config).connects_symm 1 2 |>.mpr
        hconnects)).symm
  · exact SimpleGraph.Reachable.refl _


end
end StatMech.FK.PeriodicPlanar
