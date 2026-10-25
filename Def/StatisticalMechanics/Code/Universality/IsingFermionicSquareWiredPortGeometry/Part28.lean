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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part26


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

def fkIsingSquareWiredBulgeReverseStepWord : List (Fin 4) := [1, 0, 2]

noncomputable def fkIsingSquareWiredPortMacroStepWord
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) : List (Fin 4) :=
  match d.2 with
  | .west | .east => [fkIsingSquareWiredLocalStepIndex omega d]
  | .south => fkIsingSquareWiredOrdinaryBondStepWord n hn d
  | .north =>
      if d ∈ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) then
        fkIsingSquareWiredBulgeReverseStepWord
      else fkIsingSquareWiredOrdinaryBondStepWord n hn d

end
end StatMech.Universality
