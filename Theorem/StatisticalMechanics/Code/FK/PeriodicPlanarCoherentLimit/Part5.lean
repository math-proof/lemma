module
public import Def.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part18
public import Theorem.StatisticalMechanics.Code.FK.BulkDeviationProof.Part2
public import Theorem.StatisticalMechanics.Code.FK.InclusionExclusion.Part4
public import Def.StatisticalMechanics.Code.FK.PeriodicPlanarCoherentLimit.Part5
open Finset Set SimpleGraph MeasureTheory Filter Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace FK

namespace PeriodicPlanar

variable {V : Type*} [DecidableEq V]

theorem PeriodicGraph.bufferedAdjMatch (P : PeriodicGraph V) (n : ℕ) :
    ocd_AdjMatch (P.bufferedGraph n) (P.bufferedGraph (n + 1))
      (P.bufferedVertexIncl n) := by
  intro x y
  rfl


end PeriodicPlanar
end FK
end StatMech
