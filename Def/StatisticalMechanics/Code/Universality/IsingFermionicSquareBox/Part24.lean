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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part25


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareCutBondMateEquiv (n : Nat) (hn : 0 < n) :
    Equiv.Perm (FKIsingSquareMedialCarrier n) where
  toFun := fkIsingSquareCutBondMate n hn
  invFun := fkIsingSquareCutBondMate n hn
  left_inv := fkIsingSquareCutBondMate_involutive n hn
  right_inv := fkIsingSquareCutBondMate_involutive n hn

end
end StatMech.Universality
