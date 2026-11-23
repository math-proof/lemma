/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/ClosedCurves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.DifferentialGeometry.code.PlaneCurves.Part4
public import Theorem.Real.Atlas.v1.DifferentialGeometry.code.PlaneCurves
public import Theorem.Real.Atlas.v1.DifferentialGeometry.code.DegreeTheory
public import Theorem.v1.Atlas.DifferentialGeometry.code.Reparametrization
public import Def.v1.Atlas.DifferentialGeometry.code.DegreeTheory


public noncomputable section

open Finset BigOperators MeasureTheory

namespace ClosedCurves

structure IsClosedCurve (c : ℝ → Fin 2 → ℝ) (T : ℝ) : Prop where
  smooth : ContDiff ℝ ⊤ c
  period_pos : T > 0
  periodic : ∀ t, c (t + T) = c t
  regular : ∀ t, deriv c t ≠ 0

end ClosedCurves
end
