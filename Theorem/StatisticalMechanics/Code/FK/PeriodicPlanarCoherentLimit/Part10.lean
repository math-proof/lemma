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
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarCoherentLimit.Part10
open Finset Set SimpleGraph MeasureTheory Filter Topology


namespace StatMech

namespace FK

namespace PeriodicPlanar

variable {V : Type*} [DecidableEq V]

variable [Countable V]


theorem PeriodicGraph.freeBufferedInfiniteVolume_isLimit
    (P : PeriodicGraph V) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      WeakConvergesTo (fun n => P.freeBufferedMeasure (phi n) hp hp1 hq)
        (P.freeBufferedInfiniteVolume hp hp1 hq) := by
  obtain ⟨phi, hphi, hlimit⟩ :=
    (prokhorov_seq_compact
      (fun n => P.freeBufferedMeasure n hp hp1 hq)).choose_spec
  exact ⟨phi, hphi, hlimit⟩


end PeriodicPlanar
end FK
end StatMech
