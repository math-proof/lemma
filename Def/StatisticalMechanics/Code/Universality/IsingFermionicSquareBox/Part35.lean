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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part37


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareExplorationTransitionTurn (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x y : FKIsingSquareMedialCarrier n) : Int :=
  match x, y with
  | .source, .dart f =>
      fkIsingSquareSignedEighthTurn
        (fkIsingSquareCarrierTangentCode n hn .source)
        (fkIsingSquareCarrierTangentCode n hn (.dart f) + 4)
  | .dart d, .terminal =>
      fkIsingSquareSignedEighthTurn
        (fkIsingSquareCarrierTangentCode n hn (.dart d))
        (fkIsingSquareCarrierTangentCode n hn .terminal)
  | .dart d, .dart f =>
      if f = FKIsingMedialDart.localMate omega d then
        fkIsingSquareSignedEighthTurn
          (fkIsingSquareCarrierTangentCode n hn (.dart d) + 4)
          (fkIsingSquareCarrierTangentCode n hn (.dart f))
      else
        fkIsingSquareSignedEighthTurn
          (fkIsingSquareCarrierTangentCode n hn (.dart d))
          (fkIsingSquareCarrierTangentCode n hn (.dart f) + 4) +
            fkIsingSquareExteriorCutTurn n hn d f
  | _, _ =>
      fkIsingSquareSignedEighthTurn
        (fkIsingSquareCarrierTangentCode n hn x)
        (fkIsingSquareCarrierTangentCode n hn y)

end
end StatMech.Universality
