/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateCounterexampleBase
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateCounterexample.Part2
open Finset


namespace StatMech.Ising.LPRankFiveAggregateCounterexample

open LPRankFiveCounterexample


def SelectedCrossingTarget :=
  Fin 2 × Sigma fun j : Seam => ↑(targetSectorStates 2 j)

end StatMech.Ising.LPRankFiveAggregateCounterexample
