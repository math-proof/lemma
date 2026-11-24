module
public import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part39
public import Mathlib.Logic.Equiv.Fintype
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part12


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareWiredWalkCast
    {V : Type*} {G H : SimpleGraph V} (h : G = H)
    {u v : V} (p : G.Walk u v) : H.Walk u v := h ▸ p

end
end StatMech.Universality
