/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPointInfinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FK.TwoPoint.Part4
import Theorem.StatisticalMechanics.Code.FK.Limits
import Theorem.StatisticalMechanics.Code.Foundations.MonotoneLimit
import Def.StatisticalMechanics.Code.FK.TwoPointInfinite.Part2
open MeasureTheory Filter Topology SimpleGraph
open scoped BigOperators NNReal Topology

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open StatMech.Lattice


variable {E : Type*} [Countable E]


theorem continuous_boxRestrict (d n : ℕ) : Continuous (boxRestrict d n) :=
  continuous_pi (fun eb => continuous_apply (edgeIncl d n eb))


theorem monotone_boxRestrict (d n : ℕ) : Monotone (boxRestrict d n) :=
  fun _ _ hab eb => hab (edgeIncl d n eb)


end FK
end StatMech
