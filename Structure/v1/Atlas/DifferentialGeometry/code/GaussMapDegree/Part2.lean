/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/GaussMapDegree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Def.v1.Atlas.DifferentialGeometry.code.GaussMapDegree.Part2


public noncomputable section

open scoped Matrix

namespace GaussMapDegree

structure SmoothMapBetweenHypersurfaces (n : ℕ) where
  φ : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)
  φ_smooth : ContDiff ℝ ⊤ φ
  M : Set (Fin (n + 1) → ℝ)
  M_compact : IsCompact M
  M_hypersurface : IsSmHypersurface n M
  M_oriented : ∃ ν : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ),
    Continuous ν ∧ ∀ p ∈ M, ‖ν p‖ = 1
  M_tilde : Set (Fin (n + 1) → ℝ)
  M_tilde_compact : IsCompact M_tilde
  M_tilde_connected : IsConnected M_tilde
  M_tilde_hypersurface : IsSmHypersurface n M_tilde
  M_tilde_oriented : ∃ ν : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ),
    Continuous ν ∧ ∀ p ∈ M_tilde, ‖ν p‖ = 1
  φ_maps_to_target : ∀ p ∈ M, φ p ∈ M_tilde

end GaussMapDegree
end
