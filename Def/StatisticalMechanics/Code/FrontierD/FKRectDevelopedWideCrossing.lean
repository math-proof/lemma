/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquare.Part11
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Universality.BXPAspectTransfer
open Set


namespace StatMech.FrontierD

open StatMech.Lattice

open StatMech.RSW.Box

noncomputable section

def fkRectDevelopedRectangleHorizontalCrossingEvent
    (R : FKRectTorus) (placement : Nat) (a b c d : Int) :
    Set R.Configuration :=
  fkRectDevelopedSquarePullback R placement ⁻¹'
    horizontalCrossingEvent a b c d


def fkRectDevelopedRectangleVerticalCrossingEvent
    (R : FKRectTorus) (placement : Nat) (a b c d : Int) :
    Set R.Configuration :=
  fkRectDevelopedSquarePullback R placement ⁻¹'
    verticalCrossingEvent a b c d

end
end StatMech.FrontierD
