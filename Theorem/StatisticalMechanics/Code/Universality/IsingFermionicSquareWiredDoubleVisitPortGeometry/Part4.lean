/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredDoubleVisitPortGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part34
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredOpenFibers
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredDoubleVisitPortGeometry.Part3


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareWired_fermionicObservable_contour_relation
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    let D := fkIsingSquareWiredDobrushinDomain n hn
    let edges := fkIsingSquareWiredLocalCarrierDarts n e
    D.fermionicObservable (edges 0) - D.fermionicObservable (edges 1) =
      Complex.I *
        (D.fermionicObservable (edges 2) - D.fermionicObservable (edges 3)) := by
  let D := fkIsingSquareWiredDobrushinDomain n hn
  let L := fkIsingSquareWired_exhaustiveSwitchingLaw n hn e
  simpa only [D, L, fkIsingSquareWired_exhaustiveSwitchingLaw] using
    L.fermionicObservable_contour_relation D


theorem fkIsingSquareWired_double_visit_discarded_carrier_cycle_turn_mod_sixteen
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    (∃ c : (fkIsingSquareWiredCompletedLoopGraph n hn
          (setOpen e.1 omega)).Walk
            (.dart (e, .west)) (.dart (e, .west)),
        c.IsCycle ∧ c.snd = (.dart (e, .north) :
          FKIsingSquareWiredCarrier n) ∧
        carrierAdjacentSum
          (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega))
          c.support ≡ 8 [ZMOD 16]) ∨
      (∃ c : (fkIsingSquareWiredCompletedLoopGraph n hn
          (setOpen e.1 omega)).Walk
            (.dart (e, .east)) (.dart (e, .east)),
        c.IsCycle ∧ c.snd = (.dart (e, .south) :
          FKIsingSquareWiredCarrier n) ∧
        carrierAdjacentSum
          (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega))
          c.support ≡ 8 [ZMOD 16]) := by
  let opened := setOpen e.1 omega
  rcases fkIsingSquareWired_double_visit_open_pair_exact
      n hn omega e hwest heast with
    ⟨hW, _hN, _hE, _hS⟩ | ⟨_hW, _hN, hE, _hS⟩
  · right
    let d : FKIsingMedialDart (fkSquareBoxPlanar n) := (e, .east)
    have hroot : ¬(fkIsingSquareWiredCompletedLoopGraph n hn opened).Reachable
        (fkIsingSquareWiredBlackOfDart n d).1 .source := by
      intro hreach
      apply _hE
      rw [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_reachable,
        ← fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff]
      simpa only [opened, d, fkIsingSquareWiredBlackOfDart] using hreach.symm
    obtain ⟨c, hc, hcSnd, hcTurn⟩ :=
      fkIsingSquareWiredCompletedGraph_exists_carrier_cycle_of_local_black_orbit
        n hn opened d hroot
    have hmod := fkIsingSquareWired_local_black_orbit_transition_turn_mod_sixteen
      n hn opened d hroot
    dsimp only at hmod
    rw [← hcTurn] at hmod
    refine ⟨c, hc, ?_, hmod⟩
    simpa [opened, d, fkIsingSquareWiredBlackOfDart,
      fkIsingSquareWiredTransitionMate, FKIsingMedialDart.localMate,
      setOpen_self] using hcSnd
  · left
    let d : FKIsingMedialDart (fkSquareBoxPlanar n) := (e, .west)
    have hroot : ¬(fkIsingSquareWiredCompletedLoopGraph n hn opened).Reachable
        (fkIsingSquareWiredBlackOfDart n d).1 .source := by
      intro hreach
      apply _hW
      rw [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_reachable,
        ← fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff]
      simpa only [opened, d, fkIsingSquareWiredBlackOfDart] using hreach.symm
    obtain ⟨c, hc, hcSnd, hcTurn⟩ :=
      fkIsingSquareWiredCompletedGraph_exists_carrier_cycle_of_local_black_orbit
        n hn opened d hroot
    have hmod := fkIsingSquareWired_local_black_orbit_transition_turn_mod_sixteen
      n hn opened d hroot
    dsimp only at hmod
    rw [← hcTurn] at hmod
    refine ⟨c, hc, ?_, hmod⟩
    simpa [opened, d, fkIsingSquareWiredBlackOfDart,
      fkIsingSquareWiredTransitionMate, FKIsingMedialDart.localMate,
      setOpen_self] using hcSnd

end
end StatMech.Universality
