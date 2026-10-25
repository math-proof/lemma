/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrothendieckGroup.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Exact
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.GrothendieckGroup
set_option maxHeartbeats 400000


noncomputable section

open CategoryTheory

namespace DegreeAdditivity

universe u

/-- The class `[M]` of a module `M` in `K^0(R)`. -/
def GrothendieckGroupK0.classOf (R : Type u) [Ring R] (M : ModuleCat.{u} R) :
    GrothendieckGroupK0 R :=
  QuotientAddGroup.mk (FreeAbelianGroup.of M)

/-- A function `φ` to an abelian group is SES-additive when `φ(B) = φ(A) + φ(C)` holds
for every short exact sequence. This is the universal property tested by `K^0`. -/
def IsSESAdditive (R : Type u) [Ring R] {G : Type*} [AddCommGroup G]
    (φ : ModuleCat.{u} R → G) : Prop :=
  ∀ (A B C : ModuleCat.{u} R) (f : A →ₗ[R] B) (g : B →ₗ[R] C),
    Function.Injective f → Function.Surjective g → Function.Exact f g →
    φ B = φ A + φ C

end DegreeAdditivity
end
