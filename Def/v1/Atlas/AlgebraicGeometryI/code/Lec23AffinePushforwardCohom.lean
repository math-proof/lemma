/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec23AffinePushforwardCohom.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.AffinePushforwardCohomology.Part2
open AlgebraicGeometry CategoryTheory Limits


noncomputable section

universe u

set_option maxHeartbeats 800000 in
/-- Proposition 44: For an affine morphism `f : X → Y` and a quasicoherent sheaf `F` on `X`,
the pushforward preserves higher cohomology: `Hⁿ(Y, f_* F) ≅ Hⁿ(X, F)`. -/
def prop44_affine_pushforward_cohom
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    (F : X.Modules) [F.IsQuasicoherent]
    [HasInjectiveResolutions X.Modules]
    [HasInjectiveResolutions Y.Modules]
    (n : ℕ) :
    ((Scheme.Modules.globalSectionsFunctor Y).rightDerived n).obj
      ((Scheme.Modules.pushforward f).obj F) ≅
    ((Scheme.Modules.globalSectionsFunctor X).rightDerived n).obj F :=
  prop44_affine_pushforward_cohomology f F n

end
