/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredExterior.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquarePrimalConnectivity.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredExterior
open SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def FKIsingSquareSwitchableEdge (n : Nat)
    (e : Sym2 (fkSquareBoxPlanar n).V) : Prop :=
  ¬ fkIsingSquareIsWiredArcEdge n e

end
end StatMech.Universality
