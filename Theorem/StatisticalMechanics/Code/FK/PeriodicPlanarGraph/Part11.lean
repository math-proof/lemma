/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Instance.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part4
open Finset Set SimpleGraph
open MeasureTheory


namespace StatMech

namespace FK

namespace PeriodicPlanar

open Lattice


variable {V : Type*} [DecidableEq V]


theorem triangular_shift_adj (z x y : Site 2) :
    triangularGraph.Adj (siteTranslate z x) (siteTranslate z y) ↔
      triangularGraph.Adj x y := by
  simp only [triangularGraph_adj, triangularAdj, siteTranslate_apply]
  have hyx : (y + z) - (x + z) = y - x := by abel
  have hxy : (x + z) - (y + z) = x - y := by abel
  rw [hyx, hxy]


end PeriodicPlanar
end FK
end StatMech
