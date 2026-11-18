module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CoherentSheaves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

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
public import Def.v1.Atlas.AlgebraicGeometryI.code.PushforwardPreservesKernel
public import Def.v1.Atlas.AlgebraicGeometryI.code.CoherentSpecFinitelyGenerated
public import Def.v1.Atlas.AlgebraicGeometryI.code.CoherentSheaves
public section

namespace CoherentSheaves

open CategoryTheory Limits AlgebraicGeometry in
/-- A sheaf of modules `F` on a scheme `X` is *coherent* if it is quasi-coherent and of
finite type. -/
class IsCoherentSheaf {X : Scheme.{u}} (F : X.Modules) : Prop where
  isQC : (F : SheafOfModules.{u} X.ringCatSheaf).IsQuasicoherent
  isFT : (F : SheafOfModules.{u} X.ringCatSheaf).IsFiniteType

end CoherentSheaves
