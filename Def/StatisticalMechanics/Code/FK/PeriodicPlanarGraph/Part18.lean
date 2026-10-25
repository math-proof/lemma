/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part15
open Finset Set SimpleGraph
open MeasureTheory


namespace StatMech

namespace FK

namespace PeriodicPlanar

open Lattice


variable {V : Type*} [DecidableEq V]


noncomputable def hexagonal : PeriodicGraph HexVertex where
  graph := hexagonalGraph
  shift := hexTranslate
  shift_zero := hexTranslate_zero
  shift_add := hexTranslate_add
  shift_adj := hexagonal_shift_adj
  fundamentalDomain := {(0, false), (0, true)}
  fundamentalDomain_nonempty := ⟨(0, false), by simp⟩
  covers v := ⟨v.1, (0, v.2), by rcases v with ⟨x, b⟩; cases b <;> simp,
    by rcases v with ⟨x, b⟩; ext <;> simp⟩
  locallyFinite := hexagonalGraph_locallyFinite

end PeriodicPlanar
end FK
end StatMech
