/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/DegreeTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open MeasureTheory intervalIntegral Real


namespace DegreeTheory

noncomputable def det2 (a b : Fin 2 → ℝ) : ℝ := a 0 * b 1 - a 1 * b 0

def OnUnitCircle (f : ℝ → Fin 2 → ℝ) : Prop := ∀ t, (f t 0) ^ 2 + (f t 1) ^ 2 = 1

noncomputable def angularVelocity (f : ℝ → Fin 2 → ℝ) (t : ℝ) : ℝ := det2 (f t) (deriv f t)

def IsAngleFunction (f : ℝ → Fin 2 → ℝ) (θ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ⊤ θ ∧ ∀ t, f t 0 = cos (θ t) ∧ f t 1 = sin (θ t)

noncomputable def degreeReal (f : ℝ → Fin 2 → ℝ) (T : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ t in (0 : ℝ)..T, det2 (f t) (deriv f t)

end DegreeTheory
