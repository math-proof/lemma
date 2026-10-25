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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredRibbon.Part4
open Equiv SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

noncomputable def fkIsingSquareWiredBlackBoundaryCycleToComponent
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    StatMech.FrontierA.PermCycleClass
        (fkIsingSquareWiredBlackBoundaryPerm n hn omega) →
      (fkIsingSquareWiredCompletedLoopGraph n hn omega).ConnectedComponent := by
  classical
  exact Quot.lift
    (fun x : FKIsingSquareWiredBlackCarrier n =>
      (fkIsingSquareWiredCompletedLoopGraph n hn omega).connectedComponentMk x.1)
    (fun x y hxy => SimpleGraph.ConnectedComponent.sound
      ((fkIsingSquareWired_blackBoundary_sameCycle_iff_reachable
        n hn omega x y).1 hxy))

end
end StatMech.Universality
