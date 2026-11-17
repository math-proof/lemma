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
public import Def.v1.Atlas.AlgebraicGeometryI.code.GrothendieckGroup.Part2
set_option maxHeartbeats 400000

public section

noncomputable section

open CategoryTheory

namespace DegreeAdditivity

universe u

/-- If `φ` is SES-additive, then the lifted homomorphism vanishes on every SES-relation. -/
lemma K0SESRelSubgroup_le_ker (R : Type u) [Ring R] {G : Type*} [AddCommGroup G]
    (φ : ModuleCat.{u} R → G) (hφ : IsSESAdditive R φ) :
    K0SESRelSubgroup R ≤ (FreeAbelianGroup.lift φ).ker := by
  rw [K0SESRelSubgroup, AddSubgroup.closure_le]
  rintro _ ⟨A, B, C, f, g, hf, hg, hex, rfl⟩
  show (FreeAbelianGroup.lift φ) (FreeAbelianGroup.of B - FreeAbelianGroup.of A -
    FreeAbelianGroup.of C) = 0
  rw [map_sub, map_sub, FreeAbelianGroup.lift_apply_of,
    FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of,
    hφ A B C f g hf hg hex]
  abel

end DegreeAdditivity
end
