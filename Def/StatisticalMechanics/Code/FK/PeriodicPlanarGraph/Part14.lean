/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Abbrev.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part2
open Finset Set SimpleGraph
open MeasureTheory


namespace StatMech

namespace FK

namespace PeriodicPlanar

open Lattice


variable {V : Type*} [DecidableEq V]


def hexagonalStep (i : Fin 3) : Site 2 :=
  ![![1, 0], ![0, 1], ![1, 1]] i

def hexagonalAdj (u v : HexVertex) : Prop :=
  (u.2 = false ∧ v.2 = true ∧ ∃ i : Fin 3, v.1 - u.1 = hexagonalStep i) ∨
  (v.2 = false ∧ u.2 = true ∧ ∃ i : Fin 3, u.1 - v.1 = hexagonalStep i)

end PeriodicPlanar
end FK
end StatMech
