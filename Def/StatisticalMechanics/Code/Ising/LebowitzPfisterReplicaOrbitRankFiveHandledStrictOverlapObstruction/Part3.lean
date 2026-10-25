/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.Part8
import Abbrev.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.Part2


namespace StatMech.Ising.LPRankFiveMultiplicityMateOverlapObstruction

def flip (y : Target) : Target :=
  ⟨1 - y.val, by omega⟩

def Related (z : StrictSource) (y : Target) : Prop := z = y

end StatMech.Ising.LPRankFiveMultiplicityMateOverlapObstruction
