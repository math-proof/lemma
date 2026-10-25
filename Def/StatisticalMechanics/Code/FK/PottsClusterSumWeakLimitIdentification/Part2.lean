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
import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWeakLimitIdentification
open Filter MeasureTheory Set Topology


namespace StatMech.FK

open Lattice Percolation

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def finiteOpenComponentVertices
    (omega : ConfigSpace (Sym2 V))
    (C : (openSub G omega).ConnectedComponent) : Finset V :=
  Finset.univ.filter fun x => (openSub G omega).connectedComponentMk x = C


noncomputable def finiteOpenComponentSums
    {q : Nat} [NeZero q] (omega : ConfigSpace (Sym2 V))
    (label : V -> Fin q) :
    (openSub G omega).ConnectedComponent -> Fin q :=
  pottsBlockSums (finiteOpenComponentVertices G omega) label

end StatMech.FK
