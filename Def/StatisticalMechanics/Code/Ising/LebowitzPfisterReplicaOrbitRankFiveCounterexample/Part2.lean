/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveCounterexample
open scoped symmDiff
open Finset


namespace StatMech.Ising

namespace LPRankFiveCounterexample

def componentStep (o : LPRankFiveCounterOrientation)
    (K : Finset LPRankFiveCounterSlot)
    (S : Finset LPRankFiveCounterVertex) : Finset LPRankFiveCounterVertex :=
  Finset.univ.filter fun v => v ∈ S ∨ ∃ u ∈ S, adjacent o K u v

def component (o : LPRankFiveCounterOrientation)
    (K : Finset LPRankFiveCounterSlot)
    (u : LPRankFiveCounterVertex) : Nat → Finset LPRankFiveCounterVertex
  | 0 => {u}
  | n + 1 => componentStep o K (component o K u n)


def reachable (o : LPRankFiveCounterOrientation)
    (K : Finset LPRankFiveCounterSlot)
    (u v : LPRankFiveCounterVertex) : Prop :=
  v ∈ component o K u 8

end LPRankFiveCounterexample
end StatMech.Ising
