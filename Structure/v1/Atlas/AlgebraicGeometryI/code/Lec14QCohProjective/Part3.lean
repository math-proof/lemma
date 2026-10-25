/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec14QCohProjective.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Theorem.v1.Atlas.AlgebraicGeometryI.code.Lec14QCohProjective
open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

universe u


noncomputable section

attribute [instance] GrMod.instAddCommGroup GrMod.instModule

namespace GrMod

variable {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜]

/-- A short exact sequence of graded modules `0 → M₁ → M₂ → M₃ → 0`, packaged with
injectivity of `f`, surjectivity of `g`, and exactness `ker g = range f`. -/
structure ShortExact (M₁ M₂ M₃ : GrMod 𝒜) where
  f : M₁.carrier →ₗ[A] M₂.carrier
  g : M₂.carrier →ₗ[A] M₃.carrier
  f_injective : Function.Injective f
  g_surjective : Function.Surjective g
  exact : LinearMap.ker g = LinearMap.range f

end GrMod
end
