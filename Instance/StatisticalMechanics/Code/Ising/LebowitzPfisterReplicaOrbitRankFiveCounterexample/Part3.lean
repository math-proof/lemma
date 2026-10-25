/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveCounterexample.Part3
open scoped symmDiff
open Finset


namespace StatMech.Ising

namespace LPRankFiveCounterexample

instance patternDecidable (o : LPRankFiveCounterOrientation)
    (A B : Finset LPRankFiveCounterVertex)
    (c : LPRankFiveCounterColoring) : Decidable (pattern o A B c) := by
  unfold pattern boundaryPattern sources colorClass rowClass
  infer_instance

instance boundaryPatternDecidable (o : LPRankFiveCounterOrientation)
    (A B : Finset LPRankFiveCounterVertex)
    (c : LPRankFiveCounterColoring) : Decidable (boundaryPattern o A B c) := by
  unfold boundaryPattern sources colorClass
  infer_instance

end LPRankFiveCounterexample
end StatMech.Ising
