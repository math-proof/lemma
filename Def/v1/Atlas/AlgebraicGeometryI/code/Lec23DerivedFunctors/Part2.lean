/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec23DerivedFunctors.lean -/

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
import Structure.v1.Atlas.AlgebraicGeometryI.code.Lec23DerivedFunctors.Part2
set_option maxHeartbeats 800000

open CategoryTheory Category Limits


noncomputable section

universe v u

namespace Lec23

attribute [instance] DeltaFunctor.additive

attribute [instance] Resolution.hasHomology Resolution.quasiIso

/-- Every injective resolution gives rise to a general resolution by forgetting injectivity. -/
def InjectiveResolution.toResolution
    {C : Type u} [Category.{v} C] [Abelian C] {M : C}
    (I : InjectiveResolution M) : Resolution M where
  cocomplex := I.cocomplex
  ι := I.ι

/-- `M` is adjusted to `F` (also called `F`-acyclic) if every higher right derived functor
of `F` vanishes on `M`. Such objects can replace injectives in computing `RⁿF`. -/
def IsAdjustedToFunctor
    {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
    {D : Type*} [Category D] [Abelian D]
    (F : C ⥤ D) [F.Additive] (M : C) : Prop :=
  ∀ (i : ℕ), 0 < i → IsZero ((F.rightDerived i).obj M)

/-- Proposition 43 (existence of canonical map): For any resolution `K` of `M`, there is a
canonical map from `Hⁿ(F(K))` to `(RⁿF)(M)`. -/
noncomputable def derived_functor_via_resolution
    {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
    {D : Type*} [Category D] [Abelian D]
    (F : C ⥤ D) [F.Additive] (n : ℕ) {X : C} (I : InjectiveResolution X) :
    (F.rightDerived n).obj X ≅
      (HomologicalComplex.homologyFunctor D _ n).obj
        ((F.mapHomologicalComplex _).obj I.cocomplex) :=
  I.isoRightDerivedObj F n

end Lec23
end
