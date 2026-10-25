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
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarCoherentLimit
open Finset Set SimpleGraph MeasureTheory Filter Topology


namespace StatMech

namespace FK

namespace PeriodicPlanar

variable {V : Type*} [DecidableEq V]

theorem PeriodicGraph.lt_nextBufferedRadius (P : PeriodicGraph V) (n : ℕ) :
    n < P.nextBufferedRadius n :=
  (P.exists_buffer_radius n).choose_spec.1

theorem PeriodicGraph.neighbor_mem_nextBufferedRadius
    (P : PeriodicGraph V) (n : ℕ) {v w : V}
    (hv : v ∈ P.orbitBox n) (hvw : P.graph.Adj v w) :
    w ∈ P.orbitBox (P.nextBufferedRadius n) :=
  (P.exists_buffer_radius n).choose_spec.2 v hv w hvw


end PeriodicPlanar
end FK
end StatMech
