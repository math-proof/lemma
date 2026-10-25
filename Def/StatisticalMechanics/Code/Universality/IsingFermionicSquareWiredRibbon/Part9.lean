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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredRibbon.Part8
open Equiv SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

noncomputable def fkIsingSquareWiredRibbonSystem (n : Nat) (hn : 0 < n) :
    StatMech.FrontierA.RibbonPermutationSystem
      (FKIsingMedialVertex (fkSquareBoxPlanar n))
      (FKIsingSquareWiredBlackCarrier n) where
  rotation := fkIsingSquareWiredBlackBoundaryPerm n hn
    (fkIsingSquareWiredConfigurationOfEdges n ∅)
  edgeFlip := fkIsingSquareWiredBlackLocalSwap n
  edgeFlip_isSwap := fkIsingSquareWiredBlackLocalSwap_isSwap n
  edgeFlip_commute := fun e f hef =>
    fkIsingSquareWiredBlackLocalSwap_commute n hef

end
end StatMech.Universality
