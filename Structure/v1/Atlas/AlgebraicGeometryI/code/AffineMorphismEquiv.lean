/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AffineMorphismEquiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Def.v1.Atlas.AlgebraicGeometryI.code.AffineMorphismEquiv
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
