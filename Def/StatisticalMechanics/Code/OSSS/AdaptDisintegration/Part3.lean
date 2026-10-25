/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptDisintegration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.AdaptMConditional.Part6
import Theorem.StatisticalMechanics.Code.OSSS.AdaptDisintegration.Part2
open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace AdaptDisintegration

open OSSS.Monotonic OSSS.Coding OSSS.GrandCoupling OSSS.GrandCouplingAssembly

open StatMech.Probability OSSS.AdaptiveTau OSSS.AdaptMConditional

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def selMap2 (n s m : ℕ) : ((Fin n → ℝ) × (Fin n → ℝ)) → (Fin n → ℝ) :=
  fun p => projInl n
    ((MeasurableEquiv.piCongrLeft (fun _ : Fin n ⊕ Fin n => ℝ) (sw2Equiv n s m)) (combine n p))


end AdaptDisintegration
end OSSS
end StatMech
