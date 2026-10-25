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
import Def.v1.Atlas.DifferentialGeometry.code.Hypersurfaces
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

end Hypersurface
end
