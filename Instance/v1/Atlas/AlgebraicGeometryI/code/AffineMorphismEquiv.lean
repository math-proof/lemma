/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AffineMorphismEquiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Structure.v1.Atlas.AlgebraicGeometryI.code.AffineMorphismEquiv

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u


namespace Prop17

/-- Category structure on quasi-coherent `O_Y`-algebras. -/
noncomputable instance instCategoryQCohAlg (Y : Scheme.{u}) : Category (QCohAlg Y) where
  Hom := QCohAlg.Hom
  id A := ⟨𝟙 A.sheaf, by simp⟩
  comp f g := ⟨f.ringHom ≫ g.ringHom,
    by rw [← Category.assoc, f.algebraMap_comp, g.algebraMap_comp]⟩
  id_comp f := by ext; simp
  comp_id f := by ext; simp
  assoc f g h := by ext; simp [Category.assoc]

end Prop17
