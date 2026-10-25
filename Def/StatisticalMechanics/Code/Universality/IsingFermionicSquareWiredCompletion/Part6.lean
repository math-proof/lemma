/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part39
import Mathlib.Logic.Equiv.Fintype
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part5


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareWiredShiftEquiv (n : Nat) (hn : 0 < n) :
    Equiv.Perm (FKIsingSquareWiredBoundaryDartIndex n) where
  toFun := fkIsingSquareWiredShift n hn
  invFun := fkIsingSquareWiredShiftInv n hn
  left_inv := fkIsingSquareWiredShift_left_inv n hn
  right_inv := fkIsingSquareWiredShift_right_inv n hn

def fkIsingSquareWiredShiftDartEquiv (n : Nat) (hn : 0 < n) :
    Equiv.Perm (FKIsingMedialDart (fkSquareBoxPlanar n)) :=
  (fkIsingSquareWiredShiftEquiv n hn).viaFintypeEmbedding
    (fkIsingSquareWiredBoundaryEmbedding n hn)


def fkIsingSquareWiredBondMateEquiv (n : Nat) (hn : 0 < n) :
    Equiv.Perm (FKIsingMedialDart (fkSquareBoxPlanar n)) :=
  (fkIsingSquareWiredShiftDartEquiv n hn) *
    (fkIsingSquareBondMateEquiv n hn) *
      (fkIsingSquareWiredShiftDartEquiv n hn).symm

def fkIsingSquareWiredBondMate (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :=
  fkIsingSquareWiredBondMateEquiv n hn d

end
end StatMech.Universality
