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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part17


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

def fkIsingSquareWiredBlackOfDart (n : Nat)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    FKIsingSquareWiredBlackCarrier n :=
  match d with
  | ⟨e, .west⟩ => ⟨.dart (e, .west), rfl⟩
  | ⟨e, .east⟩ => ⟨.dart (e, .east), rfl⟩
  | ⟨e, .south⟩ => ⟨.bond (e, .south), rfl⟩
  | ⟨e, .north⟩ => ⟨.bond (e, .north), rfl⟩


end
end StatMech.Universality
