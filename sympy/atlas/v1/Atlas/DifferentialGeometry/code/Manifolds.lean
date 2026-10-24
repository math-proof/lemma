/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Manifolds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import sympy.atlas.v1.Atlas.DifferentialGeometry.code.Hypersurfaces
import Lemma.Real.Atlas.v1.DifferentialGeometry.code.Hypersurfaces

noncomputable section

open scoped Topology
open LinearMap (ker range)
open Set Filter

structure IsDiffeomorphism
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (φ : E → F) (V : Set E) (U : Set F) : Prop where
  isOpen_source : IsOpen V
  isOpen_target : IsOpen U
  bijOn : Set.BijOn φ V U
  smooth_forward : ContDiffOn ℝ ⊤ φ V
  smooth_inverse : ∃ g : F → E, ContDiffOn ℝ ⊤ g U ∧
    (∀ x ∈ V, g (φ x) = x) ∧ (∀ y ∈ U, φ (g y) = y)

variable {n : ℕ}

namespace Hypersurface

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure IsLocalDefiningFunction (ψ : E → ℝ) (M : Set E) (y : E) : Prop where
  exists_open_nhd : ∃ U : Set E, IsOpen U ∧ y ∈ U ∧
    ContDiffOn ℝ 1 ψ U ∧ (∀ x ∈ U, x ∈ M ↔ ψ x = 0)
  fderiv_ne_zero : fderiv ℝ ψ y ≠ 0

def IsHypersurface (M : Set E) : Prop :=
  ∀ y ∈ M, ∃ ψ : E → ℝ, IsLocalDefiningFunction ψ M y

def tangentSpace (ψ : E → ℝ) (y : E) : Submodule ℝ E :=
  LinearMap.ker (fderiv ℝ ψ y).toLinearMap

def IsRegularPoint (ψ : E → ℝ) (y : E) : Prop :=
  DifferentiableAt ℝ ψ y ∧ fderiv ℝ ψ y ≠ 0

structure IsSmoothLocalDefiningFunction (ψ : E → ℝ) (M : Set E) (y : E) : Prop where
  exists_open_nhd : ∃ V : Set E, IsOpen V ∧ y ∈ V ∧
    ContDiffOn ℝ ⊤ ψ V ∧
    (∀ x ∈ V, x ∈ M ↔ ψ x = 0) ∧
    (∀ x ∈ V, x ∈ M → fderiv ℝ ψ x ≠ 0)

def IsHypersurfaceSubset (M : Set E) : Prop :=
  ∀ y ∈ M, ∃ ψ : E → ℝ, IsSmoothLocalDefiningFunction ψ M y

def IsConvexHypersurface (M : Set E) : Prop :=
  IsHypersurface M ∧
  ∀ y ∈ M, ∃ ψ : E → ℝ, IsLocalDefiningFunction ψ M y ∧
    (∀ z ∈ M, fderiv ℝ ψ y (z - y) ≤ 0)

end Hypersurface

namespace Hypersurface

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure IsPartialParametrization
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (M : Set E) where
  ambientNhd : Set E
  ambientNhd_open : IsOpen ambientNhd
  paramDomain : Set F
  paramDomain_open : IsOpen paramDomain
  f : F → E
  smooth : ContDiffOn ℝ ⊤ f paramDomain
  injective : Set.InjOn f paramDomain
  image_eq : f '' paramDomain = M ∩ ambientNhd
  immersion : ∀ x ∈ paramDomain, Function.Injective (fderiv ℝ f x)

def AdmitsPartialParametrization (M : Set E) (y : E) : Prop :=
  ∃ ψ : E → ℝ, IsLocalDefiningFunction ψ M y ∧
    ∃ (P : IsPartialParametrization (F := tangentSpace ψ y) M), y ∈ P.ambientNhd


end Hypersurface

namespace Hypersurface

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure IsGaussMap (ν : E → E) (M : Set E) : Prop where
  smooth : ContDiffOn ℝ ⊤ ν M
  norm_eq_one : ∀ y ∈ M, ‖ν y‖ = 1
  orthogonal_tangent : ∀ y ∈ M, ∀ ψ : E → ℝ,
    IsLocalDefiningFunction ψ M y →
      ∀ v ∈ tangentSpace ψ y, @inner ℝ _ _ (ν y) v = 0

def IsOrientable (M : Set E) : Prop :=
  ∃ ν : E → E, IsGaussMap ν M

structure OrientedHypersurface (M : Set E) where
  isHypersurface : IsHypersurface M
  gaussMap : E → E
  isGaussMap : IsGaussMap gaussMap M

end Hypersurface

namespace Hypersurface.Curvature

open scoped InnerProductSpace
open Finset

variable {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def gaussCurvatureMatrix (ψ : E → ℝ) (y : E) (Y : Fin n → E)
    (b : OrthonormalBasis (Fin (n + 1)) ℝ E) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun j i =>
    if h : (i : ℕ) < n then
      (fderiv ℝ (fderiv ℝ ψ) y) (Y ⟨i, h⟩) (b j)
    else
      (fderiv ℝ ψ y) (b j)

def gaussCurvatureLevelSet (ψ : E → ℝ) (y : E) (Y : Fin n → E)
    (b : OrthonormalBasis (Fin (n + 1)) ℝ E) : ℝ :=
  (gaussCurvatureMatrix ψ y Y b).det / ‖fderiv ℝ ψ y‖ ^ (n + 1)

def shapeOperatorLevelSet (ψ : E → ℝ) (y : E) (Y : Fin n → E) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => (1 / ‖fderiv ℝ ψ y‖) * (fderiv ℝ (fderiv ℝ ψ) y) (Y i) (Y j)

end Hypersurface.Curvature

end


namespace Hypersurface

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure IsTangentCurve (c : ℝ → E) (M : Set E) (y v : E) : Prop where
  at_zero : c 0 = y
  hasDerivAt : HasDerivAt c v 0
  image_in_M : ∀ᶠ t in 𝓝 0, c t ∈ M
