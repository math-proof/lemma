/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredOneVisitInsertedPhase
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredTangentCode
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part32


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

def fkIsingSquareWiredMacroGauge
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) : Int :=
  let code := fkIsingSquareWiredPortMacroCodeWord n hn omega d
  let raw := fkIsingSquareSignedEighthTurn
    (fkIsingSquareWiredDirectedTangentCode n hn
      (fkIsingSquareWiredBlackOfDart n d).1)
    (code.head (fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega d))
  if 0 < raw then raw + 8 else raw

def fkIsingSquareWiredMacroTurnCoboundaryAt
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) : Prop :=
  let code := fkIsingSquareWiredPortMacroCodeWord n hn omega
  let f := fkIsingSquareWiredPortNext n hn omega
  carrierAdjacentSum fkIsingSquareSignedEighthTurn (code d) +
      fkIsingSquareSignedEighthTurn
        ((code d).getLast
          (fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega d))
        ((code (f d)).head
          (fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega (f d))) ≡
    fkIsingSquareWiredTransitionTurn n hn omega
        (fkIsingSquareWiredBlackOfDart n d).1
        (fkIsingSquareWiredTransitionMate n hn omega
          (fkIsingSquareWiredBlackOfDart n d).1) +
      fkIsingSquareWiredMacroGauge n hn omega (f d) -
      fkIsingSquareWiredMacroGauge n hn omega d [ZMOD 16]

end
end StatMech.Universality
