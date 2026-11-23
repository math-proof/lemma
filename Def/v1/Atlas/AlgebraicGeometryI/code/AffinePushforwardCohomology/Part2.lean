/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AffinePushforwardCohomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Category.Grp.Abelian
public import Instance.v1.Atlas.AlgebraicGeometryI.code.AffinePushforwardCohomology

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits


noncomputable section

universe u

/-- Naturally isomorphic additive functors have naturally isomorphic right derived functors:
if `F ≅ G` then `RⁿF ≅ RⁿG` for every `n`. -/
def rightDerivedFunctorIso
    {C : Type*} [Category C] {D : Type*} [Category D]
    [Abelian C] [Abelian D] [HasInjectiveResolutions C]
    (F G : C ⥤ D) [F.Additive] [G.Additive]
    (τ : F ≅ G) (n : ℕ) : F.rightDerived n ≅ G.rightDerived n where
  hom := NatTrans.rightDerived τ.hom n
  inv := NatTrans.rightDerived τ.inv n
  hom_inv_id := by rw [← NatTrans.rightDerived_comp, τ.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by rw [← NatTrans.rightDerived_comp, τ.inv_hom_id, NatTrans.rightDerived_id]

end
