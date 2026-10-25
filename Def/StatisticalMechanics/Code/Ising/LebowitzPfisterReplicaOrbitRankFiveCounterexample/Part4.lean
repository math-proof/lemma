/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveCounterexample.Part3
open scoped symmDiff
open Finset


namespace StatMech.Ising

namespace LPRankFiveCounterexample

def seamI : Finset LPRankFiveCounterVertex := {2, 3}

def seamJ : Finset LPRankFiveCounterVertex := {4, 5}

def ghosts : Finset LPRankFiveCounterVertex := {0, 1}

def offdiag : Finset LPRankFiveCounterVertex := seamI ∪ seamJ ∪ ghosts

def sourceStates : Finset
    (LPRankFiveCounterOrientation × LPRankFiveCounterColoring) :=
  Finset.univ.filter fun z => pattern z.1 ∅ offdiag z.2

def leftTargetStates : Finset
    (LPRankFiveCounterOrientation × LPRankFiveCounterColoring) :=
  Finset.univ.filter fun z => pattern z.1 seamI (seamJ ∪ ghosts) z.2

def rightTargetStates : Finset
    (LPRankFiveCounterOrientation × LPRankFiveCounterColoring) :=
  Finset.univ.filter fun z => pattern z.1 seamJ (seamI ∪ ghosts) z.2

def orientationLeft : LPRankFiveCounterOrientation := ⟨0, by decide⟩

def orientationRight : LPRankFiveCounterOrientation := ⟨15, by decide⟩

def saturatedColoring : LPRankFiveCounterColoring := ⟨682, by decide⟩

end LPRankFiveCounterexample
end StatMech.Ising
