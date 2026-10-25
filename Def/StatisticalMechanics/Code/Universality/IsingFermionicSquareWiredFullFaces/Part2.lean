/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredFullFaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredClosedFibers.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredRibbon.Part9
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredFullFaces


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open StatMech.FrontierA

noncomputable section

def fkIsingSquareWiredBlackFaceKey (n : Nat) :
    FKIsingSquareWiredBlackCarrier n → Option (Int × Int)
  | ⟨.dart d, _⟩ =>
      some (fkIsingSquareWedgeFaceKey n d)
  | ⟨.bond d, _⟩ =>
      some (fkIsingSquareWedgeFaceKey n d)
  | ⟨.source, _⟩ => none
  | ⟨.terminal, _⟩ => none

end
end StatMech.Universality
