/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part14
open Finset Set SimpleGraph
open MeasureTheory


namespace StatMech

namespace FK

namespace PeriodicPlanar

open Lattice


variable {V : Type*} [DecidableEq V]


theorem hexagonalAdj_symm : Symmetric hexagonalAdj := by
  intro u v h
  exact h.symm

theorem hexagonalAdj_irrefl : Std.Irrefl hexagonalAdj := by
  constructor
  rintro u (⟨hf, ht, _⟩ | ⟨hf, ht, _⟩) <;> simp_all


end PeriodicPlanar
end FK
end StatMech
