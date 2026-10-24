/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/ClosedCurves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.DifferentialGeometry.code.PlaneCurves
import Lemma.Real.Atlas.v1.DifferentialGeometry.code.PlaneCurves
import Lemma.Real.Atlas.v1.DifferentialGeometry.code.DegreeTheory
import sympy.atlas.v1.Atlas.DifferentialGeometry.code.Reparametrization
import sympy.atlas.v1.Atlas.DifferentialGeometry.code.DegreeTheory

noncomputable section

open Finset BigOperators MeasureTheory

namespace ClosedCurves

structure IsClosedCurve (c : ℝ → Fin 2 → ℝ) (T : ℝ) : Prop where
  smooth : ContDiff ℝ ⊤ c
  period_pos : T > 0
  periodic : ∀ t, c (t + T) = c t
  regular : ∀ t, deriv c t ≠ 0

def IsSimpleClosedCurve (c : ℝ → Fin 2 → ℝ) (T : ℝ) : Prop :=
  IsClosedCurve c T ∧ ∀ s t, 0 ≤ s → s < t → t < T → c s ≠ c t

def IsConvexCurve (c : ℝ → Fin 2 → ℝ) (T : ℝ) : Prop :=
  IsSimpleClosedCurve c T ∧
  ∀ (a : Fin 2 → ℝ) (b : ℝ) (t₀ : ℝ),

    (∑ i, a i * c t₀ i) = b →

    (∑ i, a i * deriv c t₀ i) = 0 →

    (∀ t, (∑ i, a i * c t i) ≤ b) ∨ (∀ t, (∑ i, a i * c t i) ≥ b)

def toEuclidean (c : ℝ → Fin 2 → ℝ) : ℝ → EuclideanSpace ℝ (Fin 2) :=
  fun t => (EuclideanSpace.equiv (Fin 2) ℝ).symm (c t)

def curvature (c : ℝ → Fin 2 → ℝ) (t : ℝ) : ℝ :=
  PlaneCurves.curvature (toEuclidean c) t

def totalCurvature (c : ℝ → Fin 2 → ℝ) (T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, curvature c t * ‖deriv (toEuclidean c) t‖

def unitTangent (c : ℝ → Fin 2 → ℝ) (t : ℝ) : Fin 2 → ℝ :=
  (‖deriv (toEuclidean c) t‖⁻¹) • deriv c t

def rotationNumber (c : ℝ → Fin 2 → ℝ) (T : ℝ) : ℝ :=
  totalCurvature c T / (2 * Real.pi)

def det2 (a b : Fin 2 → ℝ) : ℝ := DegreeTheory.det2 a b
