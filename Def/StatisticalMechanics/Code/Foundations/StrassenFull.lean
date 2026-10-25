/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/StrassenFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.Strassen
import Theorem.StatisticalMechanics.Code.Foundations.StrassenFull
open MeasureTheory Finset
open scoped RealInnerProductSpace

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false


namespace StatMech

namespace Transport

open Filter Topology


variable {P : Type*} [Fintype P] [DecidableEq P] [PartialOrder P]


def IsDown (D : Finset P) : Prop := ∀ x y, x ≤ y → y ∈ D → x ∈ D


end Transport
end StatMech
