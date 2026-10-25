/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateCounterexampleBase
open Finset


namespace StatMech.Ising.LPRankFiveAggregateCounterexample

open LPRankFiveCounterexample


def AggregateSource :=
  Sigma fun i : Seam => Sigma fun j : Seam =>
    Fin (if i = j then 0 else 1) × ↑(sourceSectorStates i j)

end StatMech.Ising.LPRankFiveAggregateCounterexample
