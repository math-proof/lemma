/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/StrassenFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.Strassen
import Theorem.StatisticalMechanics.Code.Foundations.StrassenFull.Part5
open MeasureTheory Finset
open scoped RealInnerProductSpace

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false


namespace StatMech

section ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]

open ConfigSpace Transport


noncomputable def kappaOfVec
    (c : {p : ConfigSpace E × ConfigSpace E // p.1 ≤ p.2} → ℝ) :
    Measure (ConfigSpace E × ConfigSpace E) :=
  ∑ q : {p : ConfigSpace E × ConfigSpace E // p.1 ≤ p.2},
    (ENNReal.ofReal (c q)) • Measure.dirac (q : ConfigSpace E × ConfigSpace E)

end ConfigSpace
end StatMech
