module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredClosedFibers.Part2
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredRibbon.Part9
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredFullFaces.Part8


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredFullFaces.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open StatMech.FrontierA

noncomputable section

abbrev FKIsingSquareWiredFullCycleIndex (n : Nat) :=
  FKIsingSquareInteriorCell n ⊕ Option (Fin (2 * n))

end
end StatMech.Universality
