/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWeakLimitIdentification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumContinuity.Part2
import Theorem.StatisticalMechanics.Code.FK.PottsInfiniteVolume.Part8
import Theorem.StatisticalMechanics.Code.FrontierB.FreeInfiniteMultipointES
import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWeakLimitIdentification.Part5
open Filter MeasureTheory Set Topology


namespace StatMech.FK

open Lattice Percolation

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def pottsJointCylinder
    {d q : Nat} (spinSites : Finset (Site d))
    (spinSet : Set (∀ _x : spinSites, Fin q))
    (edgeSites : Finset (Sym2 (Site d)))
    (edgeSet : Set (∀ _e : edgeSites, Bool)) :
    Set (PottsJointConfig d q) :=
  cylinder (α := fun _ : Site d => Fin q) spinSites spinSet ×ˢ
    cylinder (α := fun _ : Sym2 (Site d) => Bool) edgeSites edgeSet

end StatMech.FK
