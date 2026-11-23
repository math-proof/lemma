/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CoherentSheaves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalProperties.Submodule
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Theorem.v1.Atlas.AlgebraicGeometryI.code.IsFiniteTypeOfCoversTop
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.IsFiniteTypeOfCoversTop
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.PushforwardPreservesKernel
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.CoherentSpecFinitelyGenerated
public import Def.v1.Atlas.AlgebraicGeometryI.code.PushforwardPreservesKernel
public import Def.v1.Atlas.AlgebraicGeometryI.code.CoherentSpecFinitelyGenerated
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.Prop19PushforwardEmbedding
public import Class.v1.Atlas.AlgebraicGeometryI.code.CoherentSheaves
@[expose] public section

namespace CoherentSheaves

open CategoryTheory Limits AlgebraicGeometry in
/-- The category of `O_X`-modules on a scheme `X` is abelian. -/
noncomputable instance oX_modules_abelian (X : Scheme.{u}) :
    CategoryTheory.Abelian X.Modules :=
  inferInstanceAs <| Abelian (SheafOfModules.{u} X.ringCatSheaf)

section kernel_coherent_sheaf_section

open CategoryTheory Limits AlgebraicGeometry

/-- The kernel of a morphism between quasi-coherent sheaves is quasi-coherent. -/

end kernel_coherent_sheaf_section

open CategoryTheory Limits AlgebraicGeometry in
/-- The cokernel of a morphism between coherent sheaves on a locally Noetherian scheme is
quasi-coherent. -/
instance coherent_sheaves_abelian (R : Type*) [CommRing R] :
    CategoryTheory.Abelian (ModuleCat R) :=
  inferInstance

end CoherentSheaves
