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


noncomputable section

open scoped Matrix

namespace GaussMapDegree

def gramMatrix (n : ℕ) (σ : (Fin n → ℝ) → (Fin (n + 1) → ℝ))
    (u : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  let Dσ := fderiv ℝ σ u
  fun i j =>
    ∑ k : Fin (n + 1), Dσ (Function.update 0 i 1) k * Dσ (Function.update 0 j 1) k

def augmentedMatrix {n : ℕ} (B : Matrix (Fin (n + 1)) (Fin n) ℝ)
    (ν : Fin (n + 1) → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j =>
    if h : (j : ℕ) < n then B i ⟨j, h⟩
    else ν i

end GaussMapDegree
end
