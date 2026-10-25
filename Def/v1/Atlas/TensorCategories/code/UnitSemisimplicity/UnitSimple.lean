/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/UnitSimple.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.TensorCategories.code.UnitSemisimplicity.TensorExactness
import Lemma.Category.Atlas.v1.TensorCategories.code.UnitSemisimplicity.TensorExactness
open CategoryTheory MonoidalCategory Category CategoryTheory.Limits

universe v u w


noncomputable section

namespace TensorCategories

/-- A complete orthogonal family of idempotents in `End(𝟙_ C)` gives rise to a
biproduct decomposition `𝟙_ C ≅ ⨁ f i` whose summands split each idempotent. -/
noncomputable def biproduct_from_completeOrthogonalIdempotents {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [Preadditive C] [Abelian C]
    {n : ℕ} (e : Fin n → End (𝟙_ C))
    (hcoi : CompleteOrthogonalIdempotents e) :
    ∃ (f : Fin n → C) (ι_hom : ∀ i, f i ⟶ 𝟙_ C) (π_hom : ∀ i, 𝟙_ C ⟶ f i)
      (_ : ∀ i, ι_hom i ≫ π_hom i = 𝟙 (f i))
      (_ : ∀ i, π_hom i ≫ ι_hom i = e i)
      (hbp : HasBiproduct f),
      Nonempty (𝟙_ C ≅ @biproduct _ _ _ _ f hbp) := by

  choose Y ι_hom π_hom hretract hsplit using fun i =>
    IsIdempotentComplete.idempotents_split (𝟙_ C) (e i) (hcoi.idem i).eq

  have ortho : ∀ i j, i ≠ j → ι_hom i ≫ π_hom j = 0 := by
    intro i j hij

    have h : e j * e i = 0 := hcoi.ortho (Ne.symm hij)
    change (e i) ≫ (e j) = 0 at h
    rw [← hsplit i, ← hsplit j] at h

    rw [Category.assoc, ← Category.assoc (ι_hom i)] at h

    have step1 := congr_arg (ι_hom i ≫ ·) h
    simp only [comp_zero, ← Category.assoc] at step1
    rw [hretract i, Category.id_comp] at step1
    have step2 := congr_arg (· ≫ π_hom j) step1
    simp only [zero_comp, Category.assoc] at step2
    rw [hretract j, Category.comp_id] at step2
    exact step2

  have total : ∑ i, π_hom i ≫ ι_hom i = 𝟙 (𝟙_ C) := by
    have hc := hcoi.complete
    simp only [← hsplit] at hc
    exact hc

  let bc : Limits.Bicone Y := {
    pt := 𝟙_ C
    π := π_hom
    ι := ι_hom
    ι_π := fun j j' => by
      by_cases h : j = j'
      · subst h; simp [hretract]
      · simp [ortho j j' h, h]
  }
  have hbl : bc.IsBilimit := isBilimitOfTotal bc total
  haveI : HasFiniteBiproducts C := HasFiniteBiproducts.of_hasFiniteProducts
  have hbp : HasBiproduct Y := inferInstance
  have iso : bc.pt ≅ ⨁ Y := biproduct.uniqueUpToIso Y hbl
  change 𝟙_ C ≅ ⨁ Y at iso
  exact ⟨Y, ι_hom, π_hom, hretract, hsplit, hbp, ⟨iso⟩⟩

end TensorCategories
end
