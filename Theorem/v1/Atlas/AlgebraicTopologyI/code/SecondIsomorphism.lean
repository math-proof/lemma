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

end
end SecondIsomorphism
