/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part10
open Finset Set SimpleGraph
open MeasureTheory


namespace StatMech

namespace FK

namespace PeriodicPlanar

open Lattice


variable {V : Type*} [DecidableEq V]


theorem triangularAdj_symm : Symmetric triangularAdj := by
  rintro x y ⟨i, h⟩
  exact ⟨i, h.symm⟩

theorem triangularAdj_irrefl : Std.Irrefl triangularAdj := by
  constructor
  rintro x ⟨i, h | h⟩
  · rw [sub_self] at h
    exact triangularStep_ne_zero i h.symm
  · rw [sub_self] at h
    exact triangularStep_ne_zero i h.symm


end PeriodicPlanar
end FK
end StatMech
