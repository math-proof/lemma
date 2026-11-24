module
public import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part19
public import Theorem.StatisticalMechanics.Code.FrontierA.PermCycleQuotientCount.Part2
public import Theorem.StatisticalMechanics.Code.FrontierA.FKTutte
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredRibbon.Part5
open Equiv SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredRibbon.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareWiredBlackWest (n : Nat)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    FKIsingSquareWiredBlackCarrier n :=
  ⟨.dart (e, .west), rfl⟩

def fkIsingSquareWiredBlackEast (n : Nat)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    FKIsingSquareWiredBlackCarrier n :=
  ⟨.dart (e, .east), rfl⟩

end
end StatMech.Universality
