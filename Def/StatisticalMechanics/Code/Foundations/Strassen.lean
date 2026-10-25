/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Strassen.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.StochasticDomination
open MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false


namespace StatMech

variable {E : Type*}


def orderSet (E : Type*) : Set (ConfigSpace E × ConfigSpace E) := {p | p.1 ≤ p.2}


end StatMech
