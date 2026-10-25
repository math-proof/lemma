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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part9


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareAfterA (n : Nat) (hn : 0 < n) :
    (fkSquareBoxPlanar n).V :=
  fkIsingSquareBoundaryVertex n
    (.bottom, ⟨1, by omega⟩)


def fkIsingSquareAfterB (n : Nat) (hn : 0 < n) :
    (fkSquareBoxPlanar n).V :=
  fkIsingSquareBoundaryVertex n
    (.left, ⟨1, by omega⟩)

end
end StatMech.Universality
