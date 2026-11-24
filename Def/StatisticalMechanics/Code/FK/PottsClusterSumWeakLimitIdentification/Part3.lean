module
public import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumContinuity.Part2
public import Theorem.StatisticalMechanics.Code.FK.PottsInfiniteVolume.Part8
public import Theorem.StatisticalMechanics.Code.FrontierB.FreeInfiniteMultipointES
public import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWeakLimitIdentification.Part2
open Filter MeasureTheory Set Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWeakLimitIdentification.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FK

open Lattice Percolation

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def finiteOpenComponentRepresentative
    (omega : ConfigSpace (Sym2 V))
    (C : (openSub G omega).ConnectedComponent) : V :=
  C.out

end StatMech.FK
