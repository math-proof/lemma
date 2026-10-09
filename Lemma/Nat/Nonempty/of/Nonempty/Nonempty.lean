import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.MonoidalCategory

/--
[CategoryTheory_MonoidalCategory_nonempty_iso_of_tensor_iso_tensorUnit](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CategoryTheory_MonoidalCategory_nonempty_iso_of_tensor_iso_tensorUnit.lean)
-/
@[path]
private lemma main
  {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  {M N M' N' : C}
  {e : M ≅ M'}
-- given
  (h : Nonempty (M ⊗ N ≅ 𝟙_ C))
  (h' : Nonempty (M' ⊗ N' ≅ 𝟙_ C)) :
-- imply
  Nonempty (N ≅ N') := by
-- proof
  obtain ⟨i⟩ := h
  obtain ⟨i'⟩ := h'
  exact ⟨(ρ_ N).symm ≪≫ (Iso.refl N ⊗ᵢ i'.symm) ≪≫ (α_ N M' N').symm ≪≫
    ((β_ N M') ⊗ᵢ Iso.refl N') ≪≫ ((e.symm ⊗ᵢ Iso.refl N) ⊗ᵢ Iso.refl N') ≪≫
    (i ⊗ᵢ Iso.refl N') ≪≫ λ_ N'⟩


-- created on 2026-10-05
