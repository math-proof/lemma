/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/BasedRings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.GrothendieckRingCategorical.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.GrothendieckRingCategorical
import Lemma.Category.Atlas.v1.TensorCategories.code.GradedVec
import Lemma.Category.Atlas.v1.TensorCategories.code.TannakaReconstruction
import Theorem.v1.Atlas.TensorCategories.code.GradedVec.Part6
import Structure.v1.Atlas.TensorCategories.code.TannakaReconstruction
import Instance.v1.Atlas.TensorCategories.code.BasedRings
open Finset


namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : FusionRing ι)

/-- The third group cohomology `H³(G, A)`, realized as the quotient of normalized 3-cocycles
by the cohomology equivalence relation. -/
def GroupCohomologyH3 (G : Type*) [Group G] (A : Type*) [CommGroup A] :=
  Quotient (cocycleCohomologousSetoid G A)

/-- The inner automorphism of `G` associated to an element `g`, given by conjugation
`x ↦ g x g⁻¹`. -/
def innerAut {G : Type*} [Group G] (g : G) : G ≃* G where
  toFun x := g * x * g⁻¹
  invFun x := g⁻¹ * x * g
  left_inv x := by group
  right_inv x := by group
  map_mul' x y := by group

/-- The subgroup of inner automorphisms of `G` inside `MulAut G`. -/
def InnerAutSubgroup (G : Type*) [Group G] : Subgroup (MulAut G) where
  carrier := { φ | ∃ g : G, φ = innerAut g }
  one_mem' := ⟨1, by ext x; simp [innerAut]⟩
  mul_mem' := by
    rintro φ ψ ⟨g, rfl⟩ ⟨h, rfl⟩
    exact ⟨g * h, by ext x; simp [innerAut]; group⟩
  inv_mem' := by
    rintro φ ⟨g, rfl⟩
    exact ⟨g⁻¹, by ext x; simp [innerAut]⟩

end FusionRing
