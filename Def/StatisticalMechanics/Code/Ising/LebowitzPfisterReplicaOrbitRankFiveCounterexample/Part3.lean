/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveCounterexample.Part2
open scoped symmDiff
open Finset


namespace StatMech.Ising

namespace LPRankFiveCounterexample

def sources (o : LPRankFiveCounterOrientation)
    (K : Finset LPRankFiveCounterSlot) :
    Finset LPRankFiveCounterVertex :=
  StatMech.Sharpness.RandomCurrent.sources (ends o) K

def boundaryPattern (o : LPRankFiveCounterOrientation)
    (A B : Finset LPRankFiveCounterVertex)
    (c : LPRankFiveCounterColoring) : Prop :=
  sources o (colorClass c 0) = A ∧
    sources o (colorClass c 1) = ∅ ∧
    sources o (colorClass c 2) = B ∧
    sources o (colorClass c 3) = ∅

def pattern (o : LPRankFiveCounterOrientation)
    (A B : Finset LPRankFiveCounterVertex)
    (c : LPRankFiveCounterColoring) : Prop :=
  boundaryPattern o A B c ∧
    ¬ reachable o (rowClass c false) 0 1 ∧
    ¬ reachable o (rowClass c true) 0 1

end LPRankFiveCounterexample
end StatMech.Ising
