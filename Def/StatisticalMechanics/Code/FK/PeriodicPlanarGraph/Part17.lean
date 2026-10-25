/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Instance.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part5
open Finset Set SimpleGraph
open MeasureTheory


namespace StatMech

namespace FK

namespace PeriodicPlanar

open Lattice


variable {V : Type*} [DecidableEq V]


def hexTranslate (z : Site 2) : HexVertex ≃ HexVertex where
  toFun u := (u.1 + z, u.2)
  invFun u := (u.1 - z, u.2)
  left_inv := by intro u; ext <;> simp
  right_inv := by intro u; ext <;> simp

end PeriodicPlanar
end FK
end StatMech
