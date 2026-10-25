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
import Def.v1.Atlas.DifferentialGeometry.code.GaussMapDegree


noncomputable section

open scoped Matrix

namespace GaussMapDegree

structure SmoothHypersurfaceMap (n : ℕ) where
  domainU : Set (Fin n → ℝ)
  domainU_open : IsOpen domainU
  domainV : Set (Fin n → ℝ)
  domainV_open : IsOpen domainV
  σ : (Fin n → ℝ) → (Fin (n + 1) → ℝ)
  τ : (Fin n → ℝ) → (Fin (n + 1) → ℝ)
  σ_smooth : ContDiffOn ℝ ⊤ σ domainU
  σ_immersion : ∀ u ∈ domainU, Function.Injective (fderiv ℝ σ u)
  τ_smooth : ContDiffOn ℝ ⊤ τ domainV
  τ_immersion : ∀ v ∈ domainV, Function.Injective (fderiv ℝ τ v)
  h : (Fin n → ℝ) → (Fin n → ℝ)
  h_maps : ∀ u ∈ domainU, h u ∈ domainV
  h_smooth : ContDiffOn ℝ ⊤ h domainU
  chain_rule : ∀ u ∈ domainU,
    (Matrix.of fun (i : Fin (n + 1)) (j : Fin n) => fderiv ℝ σ u (Function.update 0 j 1) i) *
      (Matrix.of fun (i : Fin n) (j : Fin n) => fderiv ℝ h u (Function.update 0 j 1) i) =
    (Matrix.of fun (i : Fin (n + 1)) (j : Fin n) => fderiv ℝ (τ ∘ h) u (Function.update 0 j 1) i)
  ν : (Fin n → ℝ) → (Fin (n + 1) → ℝ)
  ν_tilde : (Fin n → ℝ) → (Fin (n + 1) → ℝ)
  ν_orth : ∀ u ∈ domainU, ∀ j : Fin n,
    ∑ i : Fin (n + 1), fderiv ℝ σ u (Function.update 0 j 1) i * ν u i = 0
  ν_norm : ∀ u ∈ domainU, ∑ i : Fin (n + 1), ν u i ^ 2 = 1
  ν_tilde_orth : ∀ v ∈ domainV, ∀ j : Fin n,
    ∑ i : Fin (n + 1), fderiv ℝ τ v (Function.update 0 j 1) i * ν_tilde v i = 0
  ν_tilde_norm : ∀ v ∈ domainV, ∑ i : Fin (n + 1), ν_tilde v i ^ 2 = 1
  σ_pos_oriented : ∀ u ∈ domainU,
    0 < (augmentedMatrix (fun i j => fderiv ℝ σ u (Function.update 0 j 1) i)
      (ν u)).det
  τ_pos_oriented : ∀ v ∈ domainV,
    0 < (augmentedMatrix (fun i j => fderiv ℝ τ v (Function.update 0 j 1) i)
      (ν_tilde v)).det

end GaussMapDegree
end
