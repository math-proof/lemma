module
public import Mathlib
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section5
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.LocalityPrinciple
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section5.Part6
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
public import Def.v1.Atlas.AlgebraicTopologyI.code.LocalityPrinciple.Part5
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section10.Part20
open CategoryTheory CategoryTheory.Limits AlgebraicTopologyI


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace BrouwerFixedPoint

open Metric Set Inner

variable {X : Type u} [TopologicalSpace X]

/-- Multiplicativity of degree: `deg(e₁ ∘ e₂) = deg(e₁) · deg(e₂)`. -/
lemma degreeOfEndo_comp {G : AddCommGrpCat} (φ : G ≅ AddCommGrpCat.of ℤ)
    (e₁ e₂ : G ⟶ G) :
    degreeOfEndo φ (e₁ ≫ e₂) = degreeOfEndo φ e₁ * degreeOfEndo φ e₂ := by
  simp only [degreeOfEndo]
  have hfact : (φ.inv ≫ (e₁ ≫ e₂) ≫ φ.hom : AddCommGrpCat.of ℤ ⟶ _) =
      (φ.inv ≫ e₁ ≫ φ.hom) ≫ (φ.inv ≫ e₂ ≫ φ.hom) := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have h1 : ((φ.inv ≫ (e₁ ≫ e₂) ≫ φ.hom : AddCommGrpCat.of ℤ ⟶ _) (1 : ℤ)) =
      ((φ.inv ≫ e₂ ≫ φ.hom) ((φ.inv ≫ e₁ ≫ φ.hom) (1 : ℤ))) := by
    rw [hfact]; rfl
  rw [h1, addCommGrpCat_endZ_apply (φ.inv ≫ e₂ ≫ φ.hom)]
  ring

/-- The degree of the identity endomorphism is `1`. -/
lemma degreeOfEndo_id {G : AddCommGrpCat} (φ : G ≅ AddCommGrpCat.of ℤ) :
    degreeOfEndo φ (𝟙 G) = 1 := by
  simp only [degreeOfEndo, Category.id_comp, Iso.inv_hom_id]; rfl

end BrouwerFixedPoint
