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
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec23DerivedFunctors.Part2
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
