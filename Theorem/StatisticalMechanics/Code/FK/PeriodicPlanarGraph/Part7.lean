/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part9
open Finset Set SimpleGraph
open MeasureTheory


namespace StatMech

namespace FK

namespace PeriodicPlanar

open Lattice


variable {V : Type*} [DecidableEq V]


theorem triangularStep_ne_zero (i : Fin 3) : triangularStep i ≠ 0 := by
  fin_cases i <;> intro h
  · have := congrFun h 0
    norm_num [triangularStep] at this
  · have := congrFun h 1
    norm_num [triangularStep] at this
  · have := congrFun h 0
    norm_num [triangularStep] at this


end PeriodicPlanar
end FK
end StatMech
