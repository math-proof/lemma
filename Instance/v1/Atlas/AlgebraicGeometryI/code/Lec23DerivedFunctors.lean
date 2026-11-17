/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec23DerivedFunctors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Def.v1.Atlas.AlgebraicGeometryI.code.Lec23DerivedFunctors.Part2

@[expose] public section

set_option maxHeartbeats 800000

open CategoryTheory Category Limits


noncomputable section

universe v u

namespace Lec23

attribute [instance] DeltaFunctor.additive

attribute [instance] Resolution.hasHomology Resolution.quasiIso

/-- An abelian category with enough injectives admits injective resolutions. -/
instance enoughInjectives_implies_hasInjectiveResolutions
    (C : Type u) [Category.{v} C] [Abelian C] [EnoughInjectives C] :
    HasInjectiveResolutions C :=
  inferInstance

end Lec23
end
