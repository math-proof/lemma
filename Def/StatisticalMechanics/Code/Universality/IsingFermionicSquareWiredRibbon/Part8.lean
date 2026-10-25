/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredRibbon.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part19
import Theorem.StatisticalMechanics.Code.FrontierA.PermCycleQuotientCount.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.FKTutte
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredRibbon.Part7
open Equiv SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareWiredConfigurationOfEdges (n : Nat)
    (F : Finset (FKIsingMedialVertex (fkSquareBoxPlanar n))) :
    ConfigSpace (Sym2 (fkSquareBoxPlanar n).V) :=
  FK.edgeSetConfig (F.image Subtype.val)

end
end StatMech.Universality
