/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part17
open Finset Set SimpleGraph
open MeasureTheory


namespace StatMech

namespace FK

namespace PeriodicPlanar

open Lattice


variable {V : Type*} [DecidableEq V]


@[simp] theorem hexTranslate_apply (z : Site 2) (u : HexVertex) :
    hexTranslate z u = (u.1 + z, u.2) := rfl

theorem hexTranslate_zero : hexTranslate 0 = Equiv.refl HexVertex := by
  ext u <;> simp

theorem hexTranslate_add (z w : Site 2) (u : HexVertex) :
    hexTranslate (z + w) u = hexTranslate w (hexTranslate z u) := by
  ext <;> simp [add_assoc]

theorem hexagonal_shift_adj (z : Site 2) (u v : HexVertex) :
    hexagonalGraph.Adj (hexTranslate z u) (hexTranslate z v) ↔
      hexagonalGraph.Adj u v := by
  simp only [hexagonalGraph_adj, hexagonalAdj, hexTranslate_apply]
  have huv : (v.1 + z) - (u.1 + z) = v.1 - u.1 := by abel
  have hvu : (u.1 + z) - (v.1 + z) = u.1 - v.1 := by abel
  rw [huv, hvu]


end PeriodicPlanar
end FK
end StatMech
