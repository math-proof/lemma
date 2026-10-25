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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part35


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

@[simp] theorem fkIsingSquareExplorationTransitionTurn_localMate
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareExplorationTransitionTurn n hn omega (.dart d)
        (.dart (FKIsingMedialDart.localMate omega d)) =
      fkIsingSquareSignedEighthTurn
        (fkIsingSquareCarrierTangentCode n hn (.dart d) + 4)
        (fkIsingSquareCarrierTangentCode n hn
          (.dart (FKIsingMedialDart.localMate omega d))) := by
  simp [fkIsingSquareExplorationTransitionTurn]

theorem fkIsingSquareExplorationTransitionTurn_bond
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d f : FKIsingMedialDart (fkSquareBoxPlanar n))
    (h : f ≠ FKIsingMedialDart.localMate omega d) :
    fkIsingSquareExplorationTransitionTurn n hn omega
        (.dart d) (.dart f) =
      fkIsingSquareSignedEighthTurn
        (fkIsingSquareCarrierTangentCode n hn (.dart d))
        (fkIsingSquareCarrierTangentCode n hn (.dart f) + 4) +
          fkIsingSquareExteriorCutTurn n hn d f := by
    simp [fkIsingSquareExplorationTransitionTurn, h]

theorem fkIsingSquareExplorationTransitionTurn_exterior_forward
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (h : fkIsingSquareExteriorCutEnd n hn ≠
      FKIsingMedialDart.localMate omega
        (fkIsingSquareExteriorCutStart n hn)) :
    fkIsingSquareExplorationTransitionTurn n hn omega
        (.dart (fkIsingSquareExteriorCutStart n hn))
        (.dart (fkIsingSquareExteriorCutEnd n hn)) = 8 := by
  simp [fkIsingSquareExplorationTransitionTurn, h,
    fkIsingSquareExteriorCut_principal_forward,
    fkIsingSquareSignedEighthTurn]

theorem fkIsingSquareExplorationTransitionTurn_exterior_reverse
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (h : fkIsingSquareExteriorCutStart n hn ≠
      FKIsingMedialDart.localMate omega
        (fkIsingSquareExteriorCutEnd n hn)) :
    fkIsingSquareExplorationTransitionTurn n hn omega
        (.dart (fkIsingSquareExteriorCutEnd n hn))
        (.dart (fkIsingSquareExteriorCutStart n hn)) = -8 := by
  simp [fkIsingSquareExplorationTransitionTurn, h,
    fkIsingSquareExteriorCut_principal_reverse,
    fkIsingSquareSignedEighthTurn]


theorem fkIsingSquareExplorationTransitionTurn_local_table
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    (fkIsingSquareExplorationTransitionTurn n hn (setClosed e.1 omega)
      (.dart (e, .west)) (.dart (e, .south)) = -2) ∧
    (fkIsingSquareExplorationTransitionTurn n hn (setClosed e.1 omega)
      (.dart (e, .south)) (.dart (e, .west)) = 2) ∧
    (fkIsingSquareExplorationTransitionTurn n hn (setClosed e.1 omega)
      (.dart (e, .east)) (.dart (e, .north)) = -2) ∧
    (fkIsingSquareExplorationTransitionTurn n hn (setClosed e.1 omega)
      (.dart (e, .north)) (.dart (e, .east)) = 2) ∧
    (fkIsingSquareExplorationTransitionTurn n hn (setOpen e.1 omega)
      (.dart (e, .west)) (.dart (e, .north)) = 2) ∧
    (fkIsingSquareExplorationTransitionTurn n hn (setOpen e.1 omega)
      (.dart (e, .north)) (.dart (e, .west)) = -2) ∧
    (fkIsingSquareExplorationTransitionTurn n hn (setOpen e.1 omega)
      (.dart (e, .east)) (.dart (e, .south)) = 2) ∧
    (fkIsingSquareExplorationTransitionTurn n hn (setOpen e.1 omega)
      (.dart (e, .south)) (.dart (e, .east)) = -2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    cases ha : (fkIsingSquareOrientedEdge n e).axis <;>
    simp [fkIsingSquareExplorationTransitionTurn,
      fkIsingSquareCarrierTangentCode, fkIsingSquareCornerTangentCode,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner,
      FKIsingMedialDart.localMate, setOpen, setClosed,
      fkIsingSquareSignedEighthTurn,
      FKIsingSquareDirection.eighthTurn, ha]


end
end StatMech.Universality
