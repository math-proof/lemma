/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrothendieckGroup.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Exact
public import Theorem.v1.Atlas.AlgebraicGeometryI.code.GrothendieckGroup

@[expose] public section

set_option maxHeartbeats 400000


noncomputable section

open CategoryTheory

namespace DegreeAdditivity

universe u

/-- Universal property: lift an SES-additive `φ : Mod → G` to a homomorphism `K^0(R) → G`. -/
def GrothendieckGroupK0.lift (R : Type u) [Ring R] {G : Type*} [AddCommGroup G]
    (φ : ModuleCat.{u} R → G) (hφ : IsSESAdditive R φ) :
    GrothendieckGroupK0 R →+ G :=
  QuotientAddGroup.lift (K0SESRelSubgroup R) (FreeAbelianGroup.lift φ)
    (K0SESRelSubgroup_le_ker R φ hφ)

end DegreeAdditivity
end
