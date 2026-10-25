/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AdjustedResolutions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Structure.v1.Atlas.AlgebraicGeometryI.code.AdjustedResolutions


noncomputable section

open CategoryTheory Category Limits

universe v u

namespace AdjustedResolutions

attribute [instance] Resolution.hasHomology Resolution.quasiIso

/-- Every injective resolution is in particular a resolution. -/
def InjectiveResolution.toResolution
    {C : Type u} [Category.{v} C] [Abelian C] {M : C}
    (I : InjectiveResolution M) : Resolution M where
  cocomplex := I.cocomplex
  ι := I.ι

/-- Canonical map from the homology of `F(K•)` to the right derived functor `RⁿF(M)` for any
resolution `K• → M`. -/
noncomputable def prop43_injective_iso
    {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
    {D : Type*} [Category D] [Abelian D]
    (F : C ⥤ D) [F.Additive] (n : ℕ) {X : C} (I : InjectiveResolution X) :
    (F.rightDerived n).obj X ≅
      (HomologicalComplex.homologyFunctor D _ n).obj
        ((F.mapHomologicalComplex _).obj I.cocomplex) :=
  I.isoRightDerivedObj F n

/-- Independence of the choice of injective resolution: two injective resolutions of `X` give
canonically isomorphic computations of `RⁿF(X)`. -/
noncomputable def prop43_resolution_uniqueness
    {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
    {D : Type*} [Category D] [Abelian D]
    (F : C ⥤ D) [F.Additive] (n : ℕ)
    {X : C} (I J : InjectiveResolution X) :
    (HomologicalComplex.homologyFunctor D _ n).obj
        ((F.mapHomologicalComplex _).obj I.cocomplex) ≅
      (HomologicalComplex.homologyFunctor D _ n).obj
        ((F.mapHomologicalComplex _).obj J.cocomplex) :=
  (I.isoRightDerivedObj F n).symm ≪≫ J.isoRightDerivedObj F n

end AdjustedResolutions
end
