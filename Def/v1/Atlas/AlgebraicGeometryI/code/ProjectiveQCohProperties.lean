/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ProjectiveQCohProperties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.Algebra.DirectSum.Basic
import Structure.v1.Atlas.AlgebraicGeometryI.code.ProjectiveQCohProperties
open CategoryTheory Limits AlgebraicGeometry

universe u


noncomputable section

namespace ProjectiveQCohProperties

variable {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

attribute [instance] ZGradedModule.instAddCommGroup ZGradedModule.instModule

namespace ZGradedModule

variable {𝒜}

/-- A graded module is finitely generated if its underlying module is. -/
def IsFG (M : ZGradedModule 𝒜) : Prop :=
  Module.Finite A M.carrier

/-- A graded module is "finite-dimensional" if only finitely many graded components
are nonzero. -/
def IsFinDim (M : ZGradedModule 𝒜) : Prop :=
  ∃ (S : Finset ℤ), ∀ d, d ∉ S → M.component d = ⊥

/-- A graded module is locally nilpotent (with respect to the irrelevant ideal) if for
every element `x`, some power of every element of the irrelevant ideal annihilates `x`. -/
def IsLocNilpotent (M : ZGradedModule 𝒜) : Prop :=
  ∀ (x : M.carrier), ∃ (d : ℕ),
    ∀ (a : A), a ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal → a ^ d • x = 0

end ZGradedModule
end ProjectiveQCohProperties
end
