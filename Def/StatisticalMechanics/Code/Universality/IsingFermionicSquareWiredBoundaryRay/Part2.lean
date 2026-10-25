/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredBoundaryRay.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredBoundaryPhase
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredBoundaryRay


namespace StatMech.Universality

open Finset Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareWiredDirectedPhase (n : Nat) (hn : 0 < n)
    (z : FKIsingSquareWiredCarrier n) : Complex :=
  Complex.exp (Complex.I *
    ((((fkIsingSquareWiredDirectedTangentCode n hn z -
      fkIsingSquareWiredDirectedTangentCode n hn .terminal : Int) : Real) *
        (Real.pi / 8) : Real) : Complex))


def fkIsingSquareWiredDirectedTangent (n : Nat) (hn : 0 < n)
    (z : FKIsingSquareWiredCarrier n) : Complex :=
  Complex.exp (-Complex.I *
    ((((fkIsingSquareWiredDirectedTangentCode n hn z -
      fkIsingSquareWiredDirectedTangentCode n hn .terminal : Int) : Real) *
        (Real.pi / 4) : Real) : Complex))

end
end StatMech.Universality
