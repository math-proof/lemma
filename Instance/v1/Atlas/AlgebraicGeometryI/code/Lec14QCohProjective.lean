/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec14QCohProjective.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Structure.v1.Atlas.AlgebraicGeometryI.code.Lec14QCohProjective.Part3

@[expose] public section

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
