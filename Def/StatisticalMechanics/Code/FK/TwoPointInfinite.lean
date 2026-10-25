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
import Theorem.StatisticalMechanics.Code.FK.TwoPointInfinite
open MeasureTheory Filter Topology SimpleGraph
open scoped BigOperators NNReal Topology

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open StatMech.Lattice


variable {E : Type*} [Countable E]


noncomputable def ivTwoPointSup (μ : ℕ → ProbabilityMeasure (ConfigSpace E))
    (A : Set (ConfigSpace E)) : NNReal :=
  ⨆ n, (μ n) A


noncomputable def ivTwoPointInf (μ : ℕ → ProbabilityMeasure (ConfigSpace E))
    (A : Set (ConfigSpace E)) : NNReal :=
  ⨅ n, (μ n) A


end FK
end StatMech
