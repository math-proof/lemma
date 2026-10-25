/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.Part8
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHandledStrictOverlapObstruction


namespace StatMech.Ising.LPRankFiveHandledStrictOverlapObstruction

def candidates (z : StrictSource) : Finset Target :=
  Finset.univ.filter (Related z)

def incoming (y : Target) : Finset StrictSource :=
  Finset.univ.filter fun z => Related z y

def incomingDegree (degree : Nat) (y : Target) : Finset StrictSource :=
  Finset.univ.filter fun z => Related z y ∧ (candidates z).card = degree


def rerouteNeighborhood (y : Target) : Finset Target :=
  insert y (insert (flip y)
    (Finset.univ.filter fun y' =>
      ∃ z, z ∈ incoming y ∧ Related z y'))


def center : HandledSource -> Target
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 2

end StatMech.Ising.LPRankFiveHandledStrictOverlapObstruction
