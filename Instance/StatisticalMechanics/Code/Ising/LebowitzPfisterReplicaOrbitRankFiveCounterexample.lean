/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveCounterexample
open scoped symmDiff
open Finset


namespace StatMech.Ising

namespace LPRankFiveCounterexample

instance adjacentDecidable (o : LPRankFiveCounterOrientation)
    (K : Finset LPRankFiveCounterSlot) : DecidableRel (adjacent o K) := by
  intro u v
  unfold adjacent
  infer_instance

end LPRankFiveCounterexample
end StatMech.Ising
