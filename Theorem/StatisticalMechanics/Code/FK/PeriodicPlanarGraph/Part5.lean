/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part7
open Finset Set SimpleGraph
open MeasureTheory


namespace StatMech

namespace FK

namespace PeriodicPlanar

open Lattice


variable {V : Type*} [DecidableEq V]


section Countable

variable [Countable V]


theorem PeriodicGraph.freeInfiniteVolume_isLimit (P : PeriodicGraph V)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      WeakConvergesTo (fun n => P.freeFiniteMeasure (phi n) hp hp1 hq)
        (P.freeInfiniteVolume hp hp1 hq) := by
  obtain ⟨phi, hphi, hlimit⟩ :=
    (prokhorov_seq_compact (fun n => P.freeFiniteMeasure n hp hp1 hq)).choose_spec
  exact ⟨phi, hphi, hlimit⟩


end Countable
end PeriodicPlanar
end FK
end StatMech
