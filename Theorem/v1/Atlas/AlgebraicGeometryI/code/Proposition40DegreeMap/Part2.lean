/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Proposition40DegreeMap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Def.v1.Atlas.AlgebraicGeometryI.code.Proposition40DegreeMap.Part2
set_option maxHeartbeats 400000

public section

noncomputable section

open CategoryTheory

namespace Proposition40

universe u v

attribute [instance] SmoothCompleteCurveCohData.catInst

attribute [instance] SmoothCompleteCurveCohData.abelInst

variable (D : SmoothCompleteCurveCohData.{u,v})

/-- The lift of `degree : CohSheaf → ℤ` to a homomorphism on the free abelian group
sends every short exact sequence relation to zero, so its kernel contains the SES
relations subgroup. -/
lemma degree_lift_ker_contains_relations :
    CohSESRelSubgroup D ≤ (FreeAbelianGroup.lift D.degree).ker := by
  rw [CohSESRelSubgroup, AddSubgroup.closure_le]
  intro x hx
  obtain ⟨S, hf, hg, hex, rfl⟩ := hx
  rw [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, map_sub,
      FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of,
      FreeAbelianGroup.lift_apply_of]
  have := @degree_additive D S hf hg hex
  omega

end Proposition40
end
