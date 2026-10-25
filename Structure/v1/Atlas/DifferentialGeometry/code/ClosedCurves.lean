/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/ClosedCurves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.DifferentialGeometry.code.PlaneCurves.Part4
import Lemma.Real.Atlas.v1.DifferentialGeometry.code.PlaneCurves
import Lemma.Real.Atlas.v1.DifferentialGeometry.code.DegreeTheory
import Theorem.v1.Atlas.DifferentialGeometry.code.Reparametrization
import Def.v1.Atlas.DifferentialGeometry.code.DegreeTheory


noncomputable section

open Finset BigOperators MeasureTheory

namespace ClosedCurves

structure IsClosedCurve (c : ℝ → Fin 2 → ℝ) (T : ℝ) : Prop where
  smooth : ContDiff ℝ ⊤ c
  period_pos : T > 0
  periodic : ∀ t, c (t + T) = c t
  regular : ∀ t, deriv c t ≠ 0

end ClosedCurves
end
