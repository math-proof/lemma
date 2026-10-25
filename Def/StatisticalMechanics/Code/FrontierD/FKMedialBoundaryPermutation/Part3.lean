/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
import Theorem.StatisticalMechanics.Code.FrontierA.PermCycleQuotientCount.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryPermutation.Part2
open SimpleGraph Equiv


namespace StatMech.FrontierD

variable {T : EvenTorus}


noncomputable def fkMedialBlackBoundaryCycleToLoop
    (pairing : FKMedialLoopPairing T) :
    StatMech.FrontierA.PermCycleClass
        (fkMedialBlackBoundaryPerm pairing) →
      (fkMedialLoopGraph T pairing).ConnectedComponent := by
  classical
  exact Quot.lift
    (fun d : FKMedialBlackDart T =>
      (fkMedialLoopGraph T pairing).connectedComponentMk d.1)
    (fun d e hde => SimpleGraph.ConnectedComponent.sound
      ((fkMedial_blackBoundary_sameCycle_iff_reachable pairing d e).1 hde))

end StatMech.FrontierD
