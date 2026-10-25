/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part18
import Theorem.StatisticalMechanics.Code.FK.BulkDeviationProof.Part2
import Theorem.StatisticalMechanics.Code.FK.InclusionExclusion.Part4
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarCoherentLimit.Part7
open Finset Set SimpleGraph MeasureTheory Filter Topology


namespace StatMech

namespace FK

namespace PeriodicPlanar

variable {V : Type*} [DecidableEq V]

variable [Countable V]


omit [Countable V] in
theorem PeriodicGraph.continuous_bufferedRestrict
    (P : PeriodicGraph V) (n : ℕ) : Continuous (P.bufferedRestrict n) := by
  exact continuous_pi fun e => continuous_apply (P.edgeIncl (P.bufferedRadius n) e)

theorem PeriodicGraph.measurable_bufferedRestrict
    (P : PeriodicGraph V) (n : ℕ) : Measurable (P.bufferedRestrict n) :=
  (P.continuous_bufferedRestrict n).measurable

omit [Countable V] in
theorem PeriodicGraph.monotone_bufferedRestrict
    (P : PeriodicGraph V) (n : ℕ) : Monotone (P.bufferedRestrict n) := by
  intro omega eta home e
  exact home _


end PeriodicPlanar
end FK
end StatMech
