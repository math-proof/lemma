/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_expectasmeasure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Inequalities.OSSS.Part6
import Theorem.StatisticalMechanics.Code.Walls.oc3_vcubeprob
import Def.StatisticalMechanics.Code.Walls.oc3_expectasmeasure
open scoped BigOperators ENNReal
open Finset MeasureTheory
open StatMech.OSSS

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Walls

variable {E : Type*} [Fintype E] [DecidableEq E]


instance oc3_siteMeasure_isProb (ν : E → Bool → ℝ) (hν : IsProbWeight ν) (e : E) :
    IsProbabilityMeasure (oc3_siteMeasure ν hν e) := by
  unfold oc3_siteMeasure; infer_instance


end Walls
end StatMech
