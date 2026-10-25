/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HomExactImpliesExact.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Class.v1.Atlas.TensorCategories.code.ModuleFunctorDefs
import Lemma.Category.Atlas.v1.TensorCategories.code.ModuleFunctorDefs
import Structure.v1.Atlas.TensorCategories.code.HomExactImpliesExact
set_option maxHeartbeats 800000

universe v₁ v₂ v₃ u₁ u₂ u₃


namespace CategoryTheory

open Category MonoidalCategory LeftModCat Limits

/-- Proposition 2.10.7(1): If the internal Hom `Hom(N, -) : M → C` is exact in the second
variable, then the module category `M` over `C` is exact. -/
@[reducible] def prop_2_10_7_hom_exact_implies_exact
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M]
    [LeftModuleCategory C M]
    (h : InternalHomExactInSecondVar C M) :
    ExactModuleCategory C M :=
  { (‹LeftModuleCategory C M›) with
    action_preserves_projective := fun P N _ => by
      constructor
      intro A B f e _


      let f' : P ⟶ h.iHom N B := h.iHomEquiv P N B f

      have hEpi : Epi (h.iHomMap N e) := h.preserves_epi N e inferInstance

      obtain ⟨g', hg'⟩ := Projective.factors f' (h.iHomMap N e)


      let g : P ⊗ᵐ N ⟶ A := (h.iHomEquiv P N A).symm g'
      use g

      apply (h.iHomEquiv P N B).injective

      rw [h.iHomEquiv_natural P N g e]

      simp only [g, Equiv.apply_symm_apply]
      exact hg' }

end CategoryTheory
