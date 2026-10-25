/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/GaussMapDegree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Hausdorff
import Structure.v1.Atlas.DifferentialGeometry.code.GaussMapDegree


noncomputable section

open scoped Matrix

namespace GaussMapDegree

def SmoothHypersurfaceMap.jacobianMatrix {n : ℕ} (Φ : SmoothHypersurfaceMap n)
    (u : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => fderiv ℝ Φ.h u (Function.update 0 j 1) i

def SmoothHypersurfaceMap.jacobianDet {n : ℕ} (Φ : SmoothHypersurfaceMap n)
    (u : Fin n → ℝ) : ℝ :=
  (Φ.jacobianMatrix u).det

def SmoothHypersurfaceMap.sourceJacobian {n : ℕ} (Φ : SmoothHypersurfaceMap n)
    (u : Fin n → ℝ) : Matrix (Fin (n + 1)) (Fin n) ℝ :=
  fun i j => fderiv ℝ Φ.σ u (Function.update 0 j 1) i

def SmoothHypersurfaceMap.composedJacobian {n : ℕ} (Φ : SmoothHypersurfaceMap n)
    (u : Fin n → ℝ) : Matrix (Fin (n + 1)) (Fin n) ℝ :=
  fun i j => fderiv ℝ (Φ.τ ∘ Φ.h) u (Function.update 0 j 1) i

def IsSmHypersurface (n : ℕ) (M : Set (Fin (n + 1) → ℝ)) : Prop :=
  ∀ p ∈ M, ∃ (U : Set (Fin n → ℝ)) (σ : (Fin n → ℝ) → Fin (n + 1) → ℝ),
    IsOpen U ∧ ContDiffOn ℝ ⊤ σ U ∧
    (∀ u ∈ U, Function.Injective (fderiv ℝ σ u)) ∧
    p ∈ σ '' U ∧ σ '' U ⊆ M

end GaussMapDegree
end
