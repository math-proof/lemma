/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Mathlib.Combinatorics.SimpleGraph.Matching
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part25


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in


theorem fkIsingSquareLoopGraph_setOpen_eq_twoEdgeSwitch
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    fkIsingSquareLoopGraph n hn (setOpen e.1 omega) =
      medialTwoEdgeSwitch
        (fkIsingSquareLoopGraph n hn (setClosed e.1 omega))
        (.dart (e, .west)) (.dart (e, .south))
        (.dart (e, .east)) (.dart (e, .north)) := by
  let W : FKIsingSquareMedialCarrier n := .dart (e, .west)
  let N : FKIsingSquareMedialCarrier n := .dart (e, .north)
  let E : FKIsingSquareMedialCarrier n := .dart (e, .east)
  let S : FKIsingSquareMedialCarrier n := .dart (e, .south)
  have hcutW : fkIsingSquareCutBondMate n hn W ≠ S := by
    simpa [W, S, FKIsingMedialDart.localMate] using
      fkIsingSquareCutBondMate_ne_localMate n hn
        (setClosed e.1 omega) (e, .west)
  have hcutS : fkIsingSquareCutBondMate n hn S ≠ W := by
    simpa [W, S, FKIsingMedialDart.localMate] using
      fkIsingSquareCutBondMate_ne_localMate n hn
        (setClosed e.1 omega) (e, .south)
  have hcutE : fkIsingSquareCutBondMate n hn E ≠ N := by
    simpa [E, N, FKIsingMedialDart.localMate] using
      fkIsingSquareCutBondMate_ne_localMate n hn
        (setClosed e.1 omega) (e, .east)
  have hcutN : fkIsingSquareCutBondMate n hn N ≠ E := by
    simpa [E, N, FKIsingMedialDart.localMate] using
      fkIsingSquareCutBondMate_ne_localMate n hn
        (setClosed e.1 omega) (e, .north)
  have hcutWr : S ≠ fkIsingSquareCutBondMate n hn W := Ne.symm hcutW
  have hcutSr : W ≠ fkIsingSquareCutBondMate n hn S := Ne.symm hcutS
  have hcutEr : N ≠ fkIsingSquareCutBondMate n hn E := Ne.symm hcutE
  have hcutNr : E ≠ fkIsingSquareCutBondMate n hn N := Ne.symm hcutN
  have hlocal_of_ne
      (d : FKIsingMedialVertex (fkSquareBoxPlanar n)) (hd : d ≠ e) side :
      FKIsingMedialDart.localMate (setOpen e.1 omega) (d, side) =
        FKIsingMedialDart.localMate (setClosed e.1 omega) (d, side) := by
    have hde : d.1 ≠ e.1 := by
      intro h
      exact hd (Subtype.ext h)
    cases h : omega d.1 <;> cases side <;>
      simp [FKIsingMedialDart.localMate, setOpen, setClosed,
        Function.update_of_ne hde, h]
  have hadj_dart
      (rho : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
      (d : FKIsingMedialDart (fkSquareBoxPlanar n))
      (z : FKIsingSquareMedialCarrier n) :
      (fkIsingSquareLoopGraph n hn rho).Adj (.dart d) z ↔
        z = .dart (FKIsingMedialDart.localMate rho d) ∨
          z = fkIsingSquareCutBondMate n hn (.dart d) := by
    constructor
    · rintro (⟨f, hdf, rfl⟩ | hbond)
      · injection hdf with h
        subst f
        exact Or.inl rfl
      · exact Or.inr hbond
    · rintro (rfl | rfl)
      · exact Or.inl ⟨d, rfl, rfl⟩
      · exact Or.inr rfl
  ext x y
  cases x with
  | source =>
      cases y <;>
        simp [fkIsingSquareLoopGraph, medialTwoEdgeSwitch, W, N, E, S,
          SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
          SimpleGraph.edge_adj]
  | terminal =>
      cases y <;>
        simp [fkIsingSquareLoopGraph, medialTwoEdgeSwitch, W, N, E, S,
          SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
          SimpleGraph.edge_adj]
  | dart d =>
      cases y with
      | source =>
          simp [fkIsingSquareLoopGraph, medialTwoEdgeSwitch, W, N, E, S,
            SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
            SimpleGraph.edge_adj]
      | terminal =>
          simp [fkIsingSquareLoopGraph, medialTwoEdgeSwitch, W, N, E, S,
            SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
            SimpleGraph.edge_adj]
      | dart f =>
          rcases d with ⟨d, ds⟩
          rcases f with ⟨f, fs⟩
          by_cases hd : d = e <;> by_cases hf : f = e
          · subst d
            subst f
            cases ds <;> cases fs <;>
              simp [hadj_dart, medialTwoEdgeSwitch, W, N, E, S,
                FKIsingMedialDart.localMate, setOpen, setClosed,
                SimpleGraph.deleteEdges_adj,
                SimpleGraph.sup_adj, SimpleGraph.edge_adj,
                hcutW, hcutN, hcutE, hcutS,
                hcutWr, hcutNr, hcutEr, hcutSr]
          · subst d
            cases ds <;>
              simp [hadj_dart, medialTwoEdgeSwitch, W, N, E, S,
                FKIsingMedialDart.localMate, setOpen, setClosed,
                SimpleGraph.deleteEdges_adj,
                SimpleGraph.sup_adj, SimpleGraph.edge_adj, hf]
          · subst f
            have hl := hlocal_of_ne d hd ds
            cases fs <;>
              simp [hadj_dart, medialTwoEdgeSwitch, W, N, E, S,
                hl, SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
                SimpleGraph.edge_adj, hd]
          · have hl := hlocal_of_ne d hd ds
            have hold :
                s((FKIsingSquareMedialCarrier.dart (d, ds)),
                    (FKIsingSquareMedialCarrier.dart (f, fs))) ∉
                  ({s(W, S), s(E, N)} :
                    Set (Sym2 (FKIsingSquareMedialCarrier n))) := by
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
              constructor <;> intro h
              · rcases Sym2.eq_iff.mp h with h | h <;>
                  exact hd
                    (Prod.mk.inj
                      (FKIsingSquareMedialCarrier.dart.inj h.1)).1
              · rcases Sym2.eq_iff.mp h with h | h <;>
                  exact hd
                    (Prod.mk.inj
                      (FKIsingSquareMedialCarrier.dart.inj h.1)).1
            rw [hadj_dart]
            rw [medialTwoEdgeSwitch, SimpleGraph.sup_adj,
              SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj]
            rw [hadj_dart]
            rw [hl]
            simp [hold, SimpleGraph.edge_adj, W, N, E, S, hd, hf]

end
end StatMech.Universality
