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
import Theorem.StatisticalMechanics.Code.FK.TwoPointInfinite.Part4
open MeasureTheory Filter Topology SimpleGraph
open scoped BigOperators NNReal Topology

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open StatMech.Lattice


variable {E : Type*} [Countable E]


noncomputable def freeIvTwoPoint (d N : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (x y : boxVerts d N) : NNReal :=
  ivTwoPointSup (fun n => freeFiniteMeasure d n hp hp1 hq) (boxConnEvent d N x y)


noncomputable def wiredIvTwoPoint (d N : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (x y : boxVerts d N) : NNReal :=
  ivTwoPointInf (fun n => wiredFiniteMeasure d n hp hp1 hq) (boxConnEvent d N x y)


end FK
end StatMech
