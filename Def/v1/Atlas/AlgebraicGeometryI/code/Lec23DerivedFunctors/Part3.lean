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
import Instance.v1.Atlas.AlgebraicGeometryI.code.Lec23DerivedFunctors
set_option maxHeartbeats 800000

open CategoryTheory Category Limits


noncomputable section

universe v u

namespace Lec23

attribute [instance] DeltaFunctor.additive

attribute [instance] Resolution.hasHomology Resolution.quasiIso

/-- The zeroth right derived functor of a left exact additive functor `F` is naturally
isomorphic to `F` itself. -/
noncomputable def H0_iso_self
    {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
    {D : Type*} [Category D] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] :
    F.rightDerived 0 ≅ F :=
  F.rightDerivedZeroIsoSelf

end Lec23
end
