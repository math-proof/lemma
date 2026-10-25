/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/AeTailInvariant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.CondDistribution.Part4
import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
import Theorem.StatisticalMechanics.Code.Foundations.AeTailInvariant
open MeasureTheory MeasurableSpace Set Filter
open scoped ENNReal symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false


namespace StatMech

open ConfigSpace

variable {E H : Type*} [Countable E] [DecidableEq E]
  [Group H] [MulAction H E]


def atiExteriorCylinderRing (window : Set E) :
    Set (Set (ConfigSpace E)) :=
  {A | ∃ (F : Finset E) (S : Set (ConfigSpace F)),
    (↑F : Set E) ⊆ windowᶜ ∧ A = MeasureTheory.cylinder F S}

end StatMech
