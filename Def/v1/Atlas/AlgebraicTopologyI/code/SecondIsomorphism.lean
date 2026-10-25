/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/SecondIsomorphism.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.v1.Atlas.AlgebraicTopologyI.code.SecondIsomorphism
open CategoryTheory CategoryTheory.Limits


namespace SecondIsomorphism

variable {C : Type*} [Category C] [Abelian C]

section

variable {A B X : C} (f : A ⟶ X) (g : B ⟶ X)

variable [Mono f] [Mono g]

/-- For monomorphisms `f : A ↪ X` and `g : B ↪ X` in an abelian category, the pullback
`A ×_X B` is canonically isomorphic to the kernel of `biprod.desc f g : A ⊕ B ⟶ X`. This is
the standard identification of intersections of subobjects via biproducts. -/
noncomputable def pullbackIsoKernelOfDesc :
    pullback f g ≅ kernel (biprod.desc f g) where
  hom := kernel.lift _ (biprod.lift (pullback.fst f g) (-pullback.snd f g)) (by
    simp only [biprod.lift_desc, Preadditive.neg_comp, pullback.condition, add_neg_cancel])
  inv := pullback.lift (kernel.ι _ ≫ biprod.fst) (-(kernel.ι _ ≫ biprod.snd))
    (kernelDesc_pullback_condition f g)
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, Category.id_comp, pullback.lift_fst (f := f) (g := g),
        kernel.lift_ι_assoc, biprod.lift_fst]
    · simp only [Category.assoc, Category.id_comp, pullback.lift_snd (f := f) (g := g)]
      rw [Preadditive.comp_neg, kernel.lift_ι_assoc, biprod.lift_snd, neg_neg]
  inv_hom_id := by
    apply (cancel_mono (kernel.ι (biprod.desc f g))).mp
    simp only [Category.assoc, Category.id_comp, kernel.lift_ι]
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst,
        pullback.lift_fst (f := f) (g := g)]
    · simp only [Category.assoc, biprod.lift_snd,
        pullback.lift_snd (f := f) (g := g), Preadditive.comp_neg, neg_neg]

end
end SecondIsomorphism
