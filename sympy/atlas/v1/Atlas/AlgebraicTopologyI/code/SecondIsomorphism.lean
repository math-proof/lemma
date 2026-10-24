/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/SecondIsomorphism.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open CategoryTheory CategoryTheory.Limits

namespace SecondIsomorphism

variable {C : Type*} [Category C] [Abelian C]

section

variable {A B X : C} (f : A ⟶ X) (g : B ⟶ X)

/-- For morphisms `f : A ⟶ X` and `g : B ⟶ X` in an abelian category, the two compositions
out of `kernel (biprod.desc f g)` through the biproduct projections satisfy the pullback
square condition (up to a sign on the second leg). This is the equation that lets us
identify the kernel of `f - g : A ⊕ B → X` with the pullback `A ×_X B`. -/
lemma kernelDesc_pullback_condition :
    (kernel.ι (biprod.desc f g) ≫ biprod.fst) ≫ f =
    (-(kernel.ι (biprod.desc f g) ≫ biprod.snd)) ≫ g := by
  simp only [Preadditive.neg_comp, Category.assoc]
  suffices kernel.ι (biprod.desc f g) ≫ biprod.fst ≫ f +
      kernel.ι (biprod.desc f g) ≫ biprod.snd ≫ g = 0 by
    exact eq_neg_of_add_eq_zero_left this
  rw [← Preadditive.comp_add]; convert kernel.condition (biprod.desc f g) using 2
  have t := biprod.total (X := A) (Y := B)
  calc biprod.fst ≫ f + biprod.snd ≫ g
      = biprod.fst ≫ (biprod.inl ≫ biprod.desc f g) +
        biprod.snd ≫ (biprod.inr ≫ biprod.desc f g) := by
          rw [biprod.inl_desc, biprod.inr_desc]
    _ = (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) ≫ biprod.desc f g := by
          rw [Preadditive.add_comp, Category.assoc, Category.assoc]
    _ = biprod.desc f g := by rw [t, Category.id_comp]

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
