/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCodingLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.GrandCouplingAssembly.Part6
import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCodingLaw.Part2
open scoped BigOperators
open MeasureTheory

set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false


namespace StatMech

namespace OSSS

namespace AdaptiveCodingLaw

open Coding GrandCoupling GrandCouplingAssembly Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def adaptiveCode (μ : ConfigSpace E → ℝ) {n : ℕ}
    (σ : ConfigSpace E → (Fin n ≃ E)) (u : Fin n → ℝ) : ConfigSpace E := by
  classical
  exact if h : ∃ x, u ∈ adaptiveFibre μ σ x then Classical.choose h else fun _ => false

end AdaptiveCodingLaw
end OSSS
end StatMech
