/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateCounterexampleBase
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateCounterexample
open Finset


namespace StatMech.Ising.LPRankFiveAggregateCounterexample

open LPRankFiveCounterexample


noncomputable def aggregateSourceEmbedding :
    AggregateSource ↪ SelectedCrossingTarget := by
  apply Classical.choice
  apply Function.Embedding.nonempty_of_card_le
  exact aggregateSource_card_le_selectedCrossingTarget

end StatMech.Ising.LPRankFiveAggregateCounterexample
