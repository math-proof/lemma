/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_36_4.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.QuasiTensorFunctor.Part5
import Lemma.Category.Atlas.v1.TensorCategories.code.QuasiTensorFunctor
import Abbrev.v1.Atlas.TensorCategories.code.QuasiBialgebra
open scoped TensorProduct
open CategoryTheory

universe u


section MonoidalNatTransHelpers

variable {C : Type*} [Category C] [MonoidalCategory C]
  {D : Type*} [Category D] [MonoidalCategory D]
  {F G H : C ⥤ D}

/-- Helper: the inverse of a monoidal natural isomorphism is again monoidal. -/
lemma isMonoidal_inv_of_isMonoidal_hom
    {lmF : F.LaxMonoidal} {lmG : G.LaxMonoidal}
    (α : F ≅ G)
    (hα : @NatTrans.IsMonoidal _ _ _ _ _ _ F G α.hom lmF lmG) :
    @NatTrans.IsMonoidal _ _ _ _ _ _ G F α.inv lmG lmF := by
  letI := lmF; letI := lmG; letI := hα; exact inferInstance

/-- Helper: the composition of monoidal natural transformations is monoidal. -/
lemma isMonoidal_comp_of_isMonoidal
    {lmF : F.LaxMonoidal} {lmG : G.LaxMonoidal} {lmH : H.LaxMonoidal}
    (α : F ⟶ G) (β : G ⟶ H)
    (hα : @NatTrans.IsMonoidal _ _ _ _ _ _ F G α lmF lmG)
    (hβ : @NatTrans.IsMonoidal _ _ _ _ _ _ G H β lmG lmH) :
    @NatTrans.IsMonoidal _ _ _ _ _ _ F H (α ≫ β) lmF lmH := by
  letI := lmF; letI := lmG; letI := lmH; letI := hα; letI := hβ
  exact NatTrans.IsMonoidal.comp α β

end MonoidalNatTransHelpers
