/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateCounterexampleBase
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateCounterexample
open Finset


namespace StatMech.Ising.LPRankFiveAggregateCounterexample

open LPRankFiveCounterexample


noncomputable instance : Fintype AggregateSource := by
  unfold AggregateSource
  infer_instance


end StatMech.Ising.LPRankFiveAggregateCounterexample
