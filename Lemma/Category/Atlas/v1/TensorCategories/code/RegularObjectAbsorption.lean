import Mathlib
import sympy.Basic
import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part8
import Lemma.Category.Atlas.v1.TensorCategories.code.FiniteTensorCategory
open Finset CategoryTheory


namespace CategoryTheory.FiniteTensorCategoryData

/--
[absorption_identity_K0_level](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/RegularObjectAbsorption.lean)
-/
@[path]
lemma absorption_identity_K0_level
  {D : FiniteTensorCategoryData}
  {fpDimZ : ℝ}
  {tensorDecomp : D.ι → D.ι → ℝ}
-- given
  (h_hom_level : ∀ (homDim : D.ι → D.ι → ℝ), ∀ j : D.ι, (∑ i : D.ι, D.fpDimSimple i * (∑ k : D.ι, tensorDecomp i k * homDim k j)) = fpDimZ * (∑ i : D.ι, D.fpDimSimple i * homDim i j)) :
-- imply
  ∀ j : D.ι, (∑ i : D.ι, D.fpDimSimple i * tensorDecomp i j) = fpDimZ * D.fpDimSimple j := by
-- proof
  intro j
  have h := h_hom_level (fun k j' => if k = j' then 1 else 0) j
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true] at h
  exact h

end CategoryTheory.FiniteTensorCategoryData

namespace CategoryTheory.FiniteTensorCategoryData

/--
[absorption_identity_K0_level_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/RegularObjectAbsorption.lean)
-/
@[path]
lemma absorption_identity_K0_level_right
  {D : FiniteTensorCategoryData}
  {fpDimZ : ℝ}
  {tensorDecompRight : D.ι → D.ι → ℝ}
-- given
  (h_hom_level_right : ∀ (homDim : D.ι → D.ι → ℝ), ∀ j : D.ι, (∑ i : D.ι, D.fpDimSimple i * (∑ k : D.ι, tensorDecompRight i k * homDim k j)) = fpDimZ * (∑ i : D.ι, D.fpDimSimple i * homDim i j)) :
-- imply
  ∀ j : D.ι, (∑ i : D.ι, D.fpDimSimple i * tensorDecompRight i j) = fpDimZ * D.fpDimSimple j := by
-- proof
  intro j
  have h := h_hom_level_right (fun k j' => if k = j' then 1 else 0) j
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true] at h
  exact h
/-- Absorption identity on the Grothendieck ring: the regular object satisfies the
expected eigenvalue relation with respect to the fusion coefficients. -/

end CategoryTheory.FiniteTensorCategoryData


-- created on 2026-10-23
