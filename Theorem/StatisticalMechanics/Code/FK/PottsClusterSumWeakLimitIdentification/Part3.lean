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
import Def.StatisticalMechanics.Code.FK.PottsClusterSumWeakLimitIdentification.Part3
open Filter MeasureTheory Set Topology


namespace StatMech.FK

open Lattice Percolation

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


@[simp]
theorem finiteOpenComponentRepresentative_component
    (omega : ConfigSpace (Sym2 V))
    (C : (openSub G omega).ConnectedComponent) :
    (openSub G omega).connectedComponentMk
        (finiteOpenComponentRepresentative G omega C) = C := by
  exact Quot.out_eq C


end StatMech.FK
