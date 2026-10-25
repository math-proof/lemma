/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_integralmap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.OSSS.Coding.Part6
import Theorem.StatisticalMechanics.Code.OSSS.GrandCoupling.Part3
import Theorem.StatisticalMechanics.Code.OSSS.MonotonicOSSS.Part3
import Def.StatisticalMechanics.Code.Walls.oc3_integralmap
open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Walls

open StatMech.OSSS.Coding StatMech.OSSS.GrandCoupling

variable {E : Type*} [Fintype E] [DecidableEq E]


instance oc3_codeLaw_isProbabilityMeasure (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E) :
    IsProbabilityMeasure (oc3_codeLaw μ σ) := by
  unfold oc3_codeLaw
  exact inferInstance


end Walls
end StatMech
