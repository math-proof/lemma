/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredFullFaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredClosedFibers.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredRibbon.Part9
import Abbrev.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredFullFaces


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open StatMech.FrontierA

noncomputable section

def fkIsingSquareInteriorCellKey (n : Nat)
    (c : FKIsingSquareInteriorCell n) : Int × Int :=
  (-(n : Int) + c.1.val, -(n : Int) + c.2.val)

def fkIsingSquareInteriorCellVertex (n : Nat)
    (c : FKIsingSquareInteriorCell n) : (fkSquareBoxPlanar n).V :=
  ⟨![-(n : Int) + c.1.val, -(n : Int) + c.2.val], by
    intro i
    fin_cases i <;> simp
    · have hi := c.1.isLt
      omega
    · have hj := c.2.isLt
      omega⟩

end
end StatMech.Universality
