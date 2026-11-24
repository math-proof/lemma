module
public import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part39
public import Mathlib.Logic.Equiv.Fintype
public import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part9


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

noncomputable instance fkIsingSquareWiredLoopGraphDecidableAdj
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    DecidableRel (fkIsingSquareWiredLoopGraph n hn omega).Adj :=
  Classical.decRel _

end
end StatMech.Universality
