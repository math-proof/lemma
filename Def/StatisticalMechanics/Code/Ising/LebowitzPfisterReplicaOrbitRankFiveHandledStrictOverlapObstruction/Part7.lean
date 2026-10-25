/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.Part8
import Abbrev.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.Part4


namespace StatMech.Ising.LPRankFiveDoubledRectangleOverlapObstruction

def flip : Target -> Target
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 3
  | ⟨3, _⟩ => 2

def Related (z : StrictSource) (y : Target) : Prop :=
  (z.val ≤ 1 ∧ (y.val = 0 ∨ y.val = 2)) ∨
    (2 ≤ z.val ∧ (y.val = 1 ∨ y.val = 3))

end StatMech.Ising.LPRankFiveDoubledRectangleOverlapObstruction
