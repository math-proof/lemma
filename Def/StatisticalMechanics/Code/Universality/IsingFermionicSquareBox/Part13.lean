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
import Inductive.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part5


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareDirectionAvailable (n : Nat)
    (u : (fkSquareBoxPlanar n).V) : FKIsingSquareDirection -> Prop
  | .east => u.1 0 < (n : Int)
  | .north => u.1 1 < (n : Int)
  | .west => -(n : Int) < u.1 0
  | .south => -(n : Int) < u.1 1

end
end StatMech.Universality
