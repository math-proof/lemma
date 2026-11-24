module
public import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWiredTruncation
public import Theorem.StatisticalMechanics.Code.FK.FKGeneralQTranslation.Part2
public import Theorem.StatisticalMechanics.Code.IsingFK.PcUpperAllDimensions
public import Def.StatisticalMechanics.Code.FK.PottsClusterSumWiredTranslatedBoundary
open Filter MeasureTheory Set SimpleGraph Topology
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredTranslatedBoundary.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FK

open Lattice Percolation IsingFK

noncomputable section

theorem finiteConnToBdryEvent_isIncreasing {V : Type*}
    (G : SimpleGraph V) (bdry : V -> Prop) (x : V) :
    IsIncreasing (finiteConnToBdryEvent G bdry x) := by
  intro omega eta hle homega
  obtain ⟨y, hy, hxy⟩ := homega
  exact ⟨y, hy, hxy.mono (openSub_mono G hle)⟩


end
end StatMech.FK
