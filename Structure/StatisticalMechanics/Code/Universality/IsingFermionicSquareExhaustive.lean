/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareExhaustive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquarePrimalConnectivity.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareExhaustive


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section

structure FKIsingSquareSwitchingGeometry (n : Nat) (hn : 0 < n) where
  oneVisitSeparated : ∀
      (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
      (e : FKIsingMedialVertex (fkSquareBoxPlanar n)),
    ((fkIsingSquarePathUsesLocalSide n hn
        (setClosed e.1 omega) e .west ∧
      ¬ fkIsingSquarePathUsesLocalSide n hn
        (setClosed e.1 omega) e .east) ∨
     (¬ fkIsingSquarePathUsesLocalSide n hn
        (setClosed e.1 omega) e .west ∧
      fkIsingSquarePathUsesLocalSide n hn
        (setClosed e.1 omega) e .east)) →
      ¬ (fkIsingSquareLiftPhysicalGraph n
            (openSub (fkSquareBoxPlanar n).G (setClosed e.1 omega)) ⊔
          fkIsingSquareWiredExteriorGadget n).Reachable
        (.physical (fkIsingSquareOrientedEdge n e).tail)
        (.physical (fkIsingSquareOrientedEdge n e).head)
  oneVisitWestPhase : ∀
      (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
      (e : FKIsingMedialVertex (fkSquareBoxPlanar n)),
    fkIsingSquarePathUsesLocalSide n hn
        (setClosed e.1 omega) e .west →
      ¬ fkIsingSquarePathUsesLocalSide n hn
        (setClosed e.1 omega) e .east →
      ((fkIsingSquareDobrushinDomain n hn).windingPhase
          (setOpen e.1 omega) (.dart (e, .west)) =
        (fkIsingSquareDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .west))) ∧
      ((fkIsingSquareDobrushinDomain n hn).windingPhase
          (setOpen e.1 omega) (.dart (e, .south)) =
        (fkIsingSquareDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .south)))
  oneVisitEastPhase : ∀
      (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
      (e : FKIsingMedialVertex (fkSquareBoxPlanar n)),
    ¬ fkIsingSquarePathUsesLocalSide n hn
        (setClosed e.1 omega) e .west →
      fkIsingSquarePathUsesLocalSide n hn
        (setClosed e.1 omega) e .east →
      ((fkIsingSquareDobrushinDomain n hn).windingPhase
          (setOpen e.1 omega) (.dart (e, .east)) =
        (fkIsingSquareDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .east))) ∧
      ((fkIsingSquareDobrushinDomain n hn).windingPhase
          (setOpen e.1 omega) (.dart (e, .north)) =
        (fkIsingSquareDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .north)))
  doubleVisitLoopTurn : ∀
      (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
      (e : FKIsingMedialVertex (fkSquareBoxPlanar n)),
    fkIsingSquarePathUsesLocalSide n hn
        (setClosed e.1 omega) e .west →
      fkIsingSquarePathUsesLocalSide n hn
        (setClosed e.1 omega) e .east →
      FKIsingSquareDiscardedLoopTurn n hn omega e


end
end StatMech.Universality
