/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part39
import Mathlib.Logic.Equiv.Fintype
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part11


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem mem_fkIsingSquareWiredExplorationTrace_iff
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareWiredCarrier n) :
    z ∈ fkIsingSquareWiredExplorationTrace n hn omega ↔
      (fkIsingSquareWiredLoopGraph n hn omega).Reachable .source z := by
  simp [fkIsingSquareWiredExplorationTrace,
    fkIsingSquareWiredExplorationFinset]

theorem fkIsingSquareWired_localMate_mem_trace_iff
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (.dart (FKIsingMedialDart.localMate omega d) :
        FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn omega ↔
      (.dart d : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn omega := by
  rw [mem_fkIsingSquareWiredExplorationTrace_iff,
    mem_fkIsingSquareWiredExplorationTrace_iff]
  have hadj : (fkIsingSquareWiredLoopGraph n hn omega).Adj (.dart d)
      (.dart (FKIsingMedialDart.localMate omega d)) := by
    exact Or.inr rfl
  exact ⟨fun h => h.trans hadj.symm.reachable,
    fun h => h.trans hadj.reachable⟩

theorem fkIsingSquareWired_closed_west_mem_iff_south
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    (.dart (e, .west) : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega) ↔
      (.dart (e, .south) : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega) := by
  have h := fkIsingSquareWired_localMate_mem_trace_iff n hn
    (setClosed e.1 omega) (e, .west)
  simpa [FKIsingMedialDart.localMate] using h.symm

theorem fkIsingSquareWired_closed_east_mem_iff_north
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    (.dart (e, .east) : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega) ↔
      (.dart (e, .north) : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega) := by
  have h := fkIsingSquareWired_localMate_mem_trace_iff n hn
    (setClosed e.1 omega) (e, .east)
  simpa [FKIsingMedialDart.localMate] using h.symm

theorem fkIsingSquareWired_open_west_mem_iff_north
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    (.dart (e, .west) : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn (setOpen e.1 omega) ↔
      (.dart (e, .north) : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn (setOpen e.1 omega) := by
  have h := fkIsingSquareWired_localMate_mem_trace_iff n hn
    (setOpen e.1 omega) (e, .west)
  simpa [FKIsingMedialDart.localMate] using h.symm

theorem fkIsingSquareWired_open_east_mem_iff_south
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    (.dart (e, .east) : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn (setOpen e.1 omega) ↔
      (.dart (e, .south) : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn (setOpen e.1 omega) := by
  have h := fkIsingSquareWired_localMate_mem_trace_iff n hn
    (setOpen e.1 omega) (e, .east)
  simpa [FKIsingMedialDart.localMate] using h.symm

set_option maxHeartbeats 1000000 in


theorem fkIsingSquareWiredLoopGraph_setOpen_eq_twoEdgeSwitch
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredLoopGraph n hn (setOpen e.1 omega) =
      medialTwoEdgeSwitch
        (fkIsingSquareWiredLoopGraph n hn (setClosed e.1 omega))
        (.dart (e, .west)) (.dart (e, .south))
        (.dart (e, .east)) (.dart (e, .north)) := by
  have hlocal_of_ne
      (d : FKIsingMedialVertex (fkSquareBoxPlanar n)) (hd : d ≠ e)
      (side : FKIsingMedialSide) :
      FKIsingMedialDart.localMate (setOpen e.1 omega) (d, side) =
        FKIsingMedialDart.localMate (setClosed e.1 omega) (d, side) := by
    have hde : d.1 ≠ e.1 := by
      intro h
      exact hd (Subtype.ext h)
    cases h : omega d.1 <;> cases side <;>
      simp [FKIsingMedialDart.localMate, setOpen, setClosed,
        Function.update_of_ne hde, h]
  ext x y
  cases x with
  | source =>
      cases y <;>
        simp [fkIsingSquareWiredLoopGraph, medialTwoEdgeSwitch,
          SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
          SimpleGraph.edge_adj, fkIsingSquareWiredTransitionMate]
  | terminal =>
      cases y <;>
        simp [fkIsingSquareWiredLoopGraph, medialTwoEdgeSwitch,
          SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
          SimpleGraph.edge_adj, fkIsingSquareWiredTransitionMate]
  | bond d =>
      cases y <;>
        simp [fkIsingSquareWiredLoopGraph, medialTwoEdgeSwitch,
          SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
          SimpleGraph.edge_adj, fkIsingSquareWiredTransitionMate,
          fkIsingSquareWiredIncidenceMate]
  | dart d =>
      cases y with
      | source =>
          simp [fkIsingSquareWiredLoopGraph, medialTwoEdgeSwitch,
            SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
            SimpleGraph.edge_adj, fkIsingSquareWiredTransitionMate,
            fkIsingSquareWiredIncidenceMate]
      | terminal =>
          simp [fkIsingSquareWiredLoopGraph, medialTwoEdgeSwitch,
            SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
            SimpleGraph.edge_adj, fkIsingSquareWiredTransitionMate,
            fkIsingSquareWiredIncidenceMate]
      | bond f =>
          simp [fkIsingSquareWiredLoopGraph, medialTwoEdgeSwitch,
            SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
            SimpleGraph.edge_adj, fkIsingSquareWiredTransitionMate,
            fkIsingSquareWiredIncidenceMate]
      | dart f =>
          rcases d with ⟨d, ds⟩
          rcases f with ⟨f, fs⟩
          by_cases hd : d = e <;> by_cases hf : f = e
          · subst d
            subst f
            cases ds <;> cases fs <;>
              simp [fkIsingSquareWiredLoopGraph, medialTwoEdgeSwitch,
                SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
                SimpleGraph.edge_adj, fkIsingSquareWiredTransitionMate,
                fkIsingSquareWiredIncidenceMate,
                FKIsingMedialDart.localMate]
          · subst d
            cases ds <;>
              simp [fkIsingSquareWiredLoopGraph, medialTwoEdgeSwitch,
                SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
                SimpleGraph.edge_adj, fkIsingSquareWiredTransitionMate,
                fkIsingSquareWiredIncidenceMate,
                FKIsingMedialDart.localMate, hf]
          · subst f
            have hl := hlocal_of_ne d hd ds
            cases fs <;>
              simp [fkIsingSquareWiredLoopGraph, medialTwoEdgeSwitch,
                SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
                SimpleGraph.edge_adj, fkIsingSquareWiredTransitionMate,
                fkIsingSquareWiredIncidenceMate, hl, hd]
          · have hl := hlocal_of_ne d hd ds
            simp [fkIsingSquareWiredLoopGraph, medialTwoEdgeSwitch,
              SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
              SimpleGraph.edge_adj, fkIsingSquareWiredTransitionMate,
              fkIsingSquareWiredIncidenceMate, hl, hd, hf]

end
end StatMech.Universality
