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
public import Def.v1.Atlas.AlgebraicGeometryI.code.AffineMorphismEquiv
public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u


namespace Prop17

/-- A *quasi-coherent `O_Y`-algebra*: a sheaf of commutative rings on `Y`, together with a
structure map from `O_Y`, whose underlying `O_Y`-module is quasi-coherent. -/
structure QCohAlg (Y : Scheme.{u}) where
  sheaf : TopCat.Sheaf CommRingCat.{u} Y
  algebraMap : Y.sheaf ⟶ sheaf
  isQCoh : (underlyingModule Y sheaf algebraMap).IsQuasicoherent

/-- A morphism of quasi-coherent `O_Y`-algebras: a map of sheaves of rings commuting with the
structure maps from `O_Y`. -/
@[ext]
structure QCohAlg.Hom {Y : Scheme.{u}} (A B : QCohAlg Y) where
  ringHom : A.sheaf ⟶ B.sheaf
  algebraMap_comp : A.algebraMap ≫ ringHom = B.algebraMap

end Prop17
