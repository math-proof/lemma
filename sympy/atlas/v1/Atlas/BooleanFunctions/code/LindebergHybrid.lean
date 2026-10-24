/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/LindebergHybrid.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.BooleanFunctions.code.InvarianceDefs

noncomputable section

open MeasureTheory Measure Finset BigOperators ENNReal

namespace BooleanFourier

def rademacherMeasure : Measure ℝ :=
  (2 : ℝ≥0∞)⁻¹ • Measure.dirac (-1 : ℝ) + (2 : ℝ≥0∞)⁻¹ • Measure.dirac (1 : ℝ)

instance rademacherMeasure_isFiniteMeasure : IsFiniteMeasure rademacherMeasure := by
  constructor
  simp only [rademacherMeasure, Measure.coe_add, Pi.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply]
  simp

instance rademacherMeasure_sigmaFinite : SigmaFinite rademacherMeasure :=
  @IsFiniteMeasure.toSigmaFinite _ _ rademacherMeasure _

def hybridMeasure (n : ℕ) (k : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun i : Fin n =>
    if i.val < k then ProbabilityTheory.gaussianReal 0 1 else rademacherMeasure)

def hybridExpectation {n : ℕ} (f : (Fin n → Bool) → ℝ) (Ψ : ℝ → ℝ) (k : ℕ) : ℝ :=
  ∫ z : Fin n → ℝ, Ψ (multilinearExtension f z) ∂(hybridMeasure n k)

def boolToRealVec {n : ℕ} (b : Fin n → Bool) : Fin n → ℝ :=
  fun i => boolToReal (b i)
