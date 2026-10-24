/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/PlaneCurves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

namespace PlaneCurves

def det2 (v w : EuclideanSpace ℝ (Fin 2)) : ℝ := v 0 * w 1 - v 1 * w 0

structure IsRegularCurve (c : ℝ → EuclideanSpace ℝ (Fin 2)) (S : Set ℝ) : Prop where
  smooth : ContDiff ℝ ⊤ c
  deriv_ne_zero : ∀ t ∈ S, deriv c t ≠ 0

def curvature (c : ℝ → EuclideanSpace ℝ (Fin 2)) (t : ℝ) : ℝ :=
  det2 (deriv c t) (deriv (deriv c) t) / ‖deriv c t‖ ^ 3

def J (v : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![- v 1, v 0]

lemma J_smul (a : ℝ) (v : EuclideanSpace ℝ (Fin 2)) : J (a • v) = a • J v := by
  ext i; fin_cases i <;> simp [smul_eq_mul]

lemma J_add (v w : EuclideanSpace ℝ (Fin 2)) : J (v + w) = J v + J w := by
  ext i; fin_cases i <;> simp; ring

def JLinearMap : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun := J
  map_add' := J_add
  map_smul' := J_smul

def JContinuous : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  LinearMap.toContinuousLinearMap JLinearMap

abbrev R2 := EuclideanSpace ℝ (Fin 2)

def hessianVec (F : R2 → ℝ) (x v : R2) : R2 :=
  fderiv ℝ (fun y => gradient F y) x v
