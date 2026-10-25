/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBond.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalIncidence
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBond


namespace StatMech.Universality

open SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareWiredBondPhase
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) : Complex :=
  Complex.exp (Complex.I *
    ((((fkIsingSquareWiredBondTurn n hn d
      (fkIsingSquareWiredBondMate n hn d) : Int) : Real) *
        (Real.pi / 8) : Real) : Complex))

end
end StatMech.Universality
