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
import Structure.v1.Atlas.AlgebraicGeometryI.code.Lec14QCohProjective.Part3
open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

universe u


noncomputable section

attribute [instance] GrMod.instAddCommGroup GrMod.instModule

/-- Category instance on graded modules over `𝒜`: morphisms are `GrMod.Hom`, identity
and composition come from the underlying linear maps. -/
instance grModCategory {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] : Category (GrMod 𝒜) where
  Hom := GrMod.Hom
  id M := ⟨LinearMap.id⟩
  comp f g := ⟨g.toLinearMap.comp f.toLinearMap⟩
  id_comp f := by apply GrMod.Hom.ext; simp
  comp_id f := by apply GrMod.Hom.ext; simp
  assoc f g h := by apply GrMod.Hom.ext; simp [LinearMap.comp_assoc]

end
