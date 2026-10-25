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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part4


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareBoundaryOrderEquiv (n : Nat) :
    FKIsingSquareBoundaryIndex n ≃ Fin (8 * n) :=
  Equiv.ofBijective (fkIsingSquareBoundaryOrderFin n)
    (fkIsingSquareBoundaryOrderFin_bijective n)


def fkIsingSquareBoundarySucc (n : Nat) (hn : 0 < n) :
    Equiv.Perm (FKIsingSquareBoundaryIndex n) :=
  (fkIsingSquareBoundaryOrderEquiv n).trans
    ((svFinitePeriodicSuccEquiv (by omega : 0 < 8 * n)).trans
      (fkIsingSquareBoundaryOrderEquiv n).symm)


def fkIsingSquareBoundaryOrder (n : Nat) :
    List (FKIsingSquareBoundaryIndex n) :=
  List.ofFn fun i : Fin (8 * n) =>
    (fkIsingSquareBoundaryOrderEquiv n).symm i

end
end StatMech.Universality
