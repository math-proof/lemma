/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/StrassenFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.Strassen
import Theorem.StatisticalMechanics.Code.Foundations.StrassenFull.Part3
open MeasureTheory Finset
open scoped RealInnerProductSpace

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false


namespace StatMech

namespace Transport

open Filter Topology


variable {P : Type*} [Fintype P] [DecidableEq P] [PartialOrder P]


variable [DecidableRel ((· ≤ ·) : P → P → Prop)]


open ProperCone Set


noncomputable def orthant (P : Type*) [Fintype P] [DecidableEq P] [PartialOrder P]
    [DecidableRel ((· ≤ ·) : P → P → Prop)] : ProperCone ℝ (EuclideanSpace ℝ (OrderPairs P)) :=
  innerDual (Set.range (fun q => (EuclideanSpace.single q 1 : EuclideanSpace ℝ (OrderPairs P))))

end Transport
end StatMech
