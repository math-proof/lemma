/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredExterior.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquarePrimalConnectivity.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredExterior
open SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

instance fkIsingSquareIsWiredArcEdge_decidable (n : Nat) :
    DecidablePred (fkIsingSquareIsWiredArcEdge n) := Classical.decPred _


end
end StatMech.Universality
