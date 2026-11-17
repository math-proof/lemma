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

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u


namespace Prop17

/-- The "absolute" anti-equivalence between affine schemes and commutative rings:
`AffineScheme ≌ CommRingᵒᵖ` via `Spec`. (Thm 2.1.) -/
noncomputable def absolute : AffineScheme.{u} ≌ CommRingCat.{u}ᵒᵖ :=
  AffineScheme.equivCommRingCat

/-- The `O_Y`-module underlying an `O_Y`-algebra `A` (with structure map `α : O_Y → A`),
obtained by restriction of scalars from the natural `A`-module structure on `A`. -/
noncomputable def underlyingModule (Y : Scheme.{u}) (A : TopCat.Sheaf CommRingCat.{u} Y)
    (α : Y.sheaf ⟶ A) : Y.Modules :=
  let F := sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat)
  (SheafOfModules.restrictScalars (F.map α)).obj (SheafOfModules.unit.{u} (F.obj A))

end Prop17
