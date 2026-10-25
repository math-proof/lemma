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
import Def.v1.Atlas.DifferentialGeometry.code.GaussMapDegree.Part3


noncomputable section

open scoped Matrix

namespace GaussMapDegree

structure SmoothMapToSphere (n : ℕ) where
  φ : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)
  φ_smooth : ContDiff ℝ ⊤ φ
  M : Set (Fin (n + 1) → ℝ)
  M_compact : IsCompact M
  M_hypersurface : IsSmHypersurface n M
  M_oriented : ∃ ν : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ),
    Continuous ν ∧ ∀ p ∈ M, ‖ν p‖ = 1
  φ_maps_to_sphere : ∀ p ∈ M, ‖φ p‖ = 1

end GaussMapDegree
end
