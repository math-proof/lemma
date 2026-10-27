import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part8
open CategoryTheory
open MonoidalCategory
open scoped TensorProduct
open TensorCategories


namespace CategoryTheory

/--
[FiniteTensorCategory.enough_projectives](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FiniteTensorCategory.lean)
-/
@[path]
lemma FiniteTensorCategory.enough_projectives
  {k : Type w}
  [Field k]
  {C : Type u}
  [Category.{v} C]
  [FiniteTensorCategory k C] :
-- imply
  EnoughProjectives C :=
-- proof
  FiniteTensorCategory.enoughProj k

end CategoryTheory

namespace CategoryTheory

/--
[FiniteTensorCategory.hom_finite_dimensional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FiniteTensorCategory.lean)
-/
@[path]
lemma FiniteTensorCategory.hom_finite_dimensional
  {k : Type w}
  [Field k]
  {C : Type u}
  [Category.{v} C]
  [FiniteTensorCategory k C]
  {X Y : C} :
-- imply
  FiniteDimensional k (X ⟶ Y) :=
-- proof
  FiniteTensorCategory.homFiniteDim X Y

end CategoryTheory

namespace CategoryTheory

/--
[Simple.indecomposable'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FiniteTensorCategory.lean)
-/
@[path]
lemma Simple.indecomposable'
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {X : C}
  [Simple X] :
-- imply
  Indecomposable X :=
-- proof
  indecomposable_of_simple X

end CategoryTheory

namespace CategoryTheory

/--
[projective_cover_simple_indecomposable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FiniteTensorCategory.lean)
-/
@[path]
lemma projective_cover_simple_indecomposable
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  [EnoughProjectives C]
  [HasProjectiveCoversOfSimples C]
  {X : C}
  [Simple X] :
-- imply
  Indecomposable (exists_projective_cover_of_simple X).1 := by
-- proof
  set cover := exists_projective_cover_of_simple X
  set P := cover.1
  set pc := cover.2
  set π := pc.π
  haveI : Projective P := pc.proj
  haveI : Epi π := pc.epi_π
  refine ⟨?_, ?_⟩
  ·
    exact fun hP => (indecomposable_of_simple X).1 (IsZero.of_epi π hP)
  ·
    intro A B φ
    set gA : A ⟶ X := biprod.inl ≫ φ.inv ≫ π
    set gB : B ⟶ X := biprod.inr ≫ φ.inv ≫ π
    have aux_B_zero : Epi gA → IsZero B := by
      intro _
      obtain ⟨s, hs⟩ := Projective.factors π gA
      set f : P ⟶ P := s ≫ biprod.inl ≫ φ.inv
      have hfπ : f ≫ π = π := by simp only [f, Category.assoc]; exact hs
      haveI := pc.minimal f hfπ
      have key : (f ≫ φ.hom) ≫ biprod.snd = 0 := by
        simp only [f, Category.assoc, Iso.inv_hom_id_assoc, biprod.inl_snd, comp_zero]
      haveI : IsIso (f ≫ φ.hom) := inferInstance
      have hsnd : (biprod.snd : A ⊞ B ⟶ B) = 0 := by
        rw [show (biprod.snd : A ⊞ B ⟶ B) = 𝟙 _ ≫ biprod.snd from (Category.id_comp _).symm,
          show 𝟙 (A ⊞ B) = inv (f ≫ φ.hom) ≫ (f ≫ φ.hom) from (IsIso.inv_hom_id _).symm,
          Category.assoc, key, comp_zero]
      rw [IsZero.iff_id_eq_zero]
      calc 𝟙 B = biprod.inr ≫ biprod.snd := biprod.inr_snd.symm
        _ = biprod.inr ≫ 0 := by rw [hsnd]
        _ = 0 := comp_zero
    have aux_A_zero : Epi gB → IsZero A := by
      intro _
      obtain ⟨s, hs⟩ := Projective.factors π gB
      set f : P ⟶ P := s ≫ biprod.inr ≫ φ.inv
      have hfπ : f ≫ π = π := by simp only [f, Category.assoc]; exact hs
      haveI := pc.minimal f hfπ
      have key : (f ≫ φ.hom) ≫ biprod.fst = 0 := by
        simp only [f, Category.assoc, Iso.inv_hom_id_assoc, biprod.inr_fst, comp_zero]
      haveI : IsIso (f ≫ φ.hom) := inferInstance
      have hfst : (biprod.fst : A ⊞ B ⟶ A) = 0 := by
        rw [show (biprod.fst : A ⊞ B ⟶ A) = 𝟙 _ ≫ biprod.fst from (Category.id_comp _).symm,
          show 𝟙 (A ⊞ B) = inv (f ≫ φ.hom) ≫ (f ≫ φ.hom) from (IsIso.inv_hom_id _).symm,
          Category.assoc, key, comp_zero]
      rw [IsZero.iff_id_eq_zero]
      calc 𝟙 A = biprod.inl ≫ biprod.fst := biprod.inl_fst.symm
        _ = biprod.inl ≫ 0 := by rw [hfst]
        _ = 0 := comp_zero
    by_cases hgA : gA = 0
    · have hgB : gB ≠ 0 := by
      intro hgB0
      have h0 : φ.inv ≫ π = 0 := by
        apply biprod.hom_ext'
        · simp [show biprod.inl ≫ (φ.inv ≫ π) = gA from by simp [gA], hgA]
        · simp [show biprod.inr ≫ (φ.inv ≫ π) = gB from by simp [gB], hgB0]
      exact (indecomposable_of_simple X).1
        (IsZero.of_epi_eq_zero π
          (by rw [show π = φ.hom ≫ (φ.inv ≫ π) from by simp, h0, comp_zero]))
      left; exact aux_A_zero (epi_of_nonzero_to_simple hgB)
    · right; exact aux_B_zero (epi_of_nonzero_to_simple hgA)

end CategoryTheory

namespace CategoryTheory

/--
[nonzero_of_epi_to_simple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FiniteTensorCategory.lean)
-/
@[path]
lemma nonzero_of_epi_to_simple
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {X Y : C}
  [Simple Y]
  {f : X ⟶ Y}
  [Epi f] :
-- imply
  f ≠ 0 := by
-- proof
  intro hf
  exact id_nonzero Y ((cancel_epi f).mp (by rw [hf]; simp))

end CategoryTheory

namespace CategoryTheory

/--
[HasRegularObject.regularObj_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FiniteTensorCategory.lean)
-/
@[path]
lemma HasRegularObject.regularObj_coeff
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [h : HasRegularObject C]
  {i : h.ι} :
-- imply
  h.regularObj.coeff i = h.fpData.fpDimSimple i := by
-- proof
  simp [regularObj]

end CategoryTheory

namespace CategoryTheory

/--
[HasRegularObject.regularCoeff_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FiniteTensorCategory.lean)
-/
@[path]
lemma HasRegularObject.regularCoeff_pos
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [h : HasRegularObject C]
  {i : h.ι} :
-- imply
  h.regularCoeff i > 0 := by
-- proof
  simp only [regularCoeff, regularObj_coeff]
  exact h.fpData.fpDimSimple_pos i

end CategoryTheory

namespace CategoryTheory

/--
[fpdimCat_ge_fpdimProjUnit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FiniteTensorCategory.lean)
-/
@[path]
lemma fpdimCat_ge_fpdimProjUnit
  {C : Type u}
  [Category.{v} C] :
-- imply
  HasCategoricalFPdim.fpdimCat (C := C) > h.fpdimProjUnit := by
-- proof
  have hN : (↑h.numSimples : ℝ) ≥ 1 := by exact_mod_cast h.numSimples_pos
  calc HasCategoricalFPdim.fpdimCat (C := C)
    > ↑h.numSimples * h.fpdimProjUnit :=
      h.fpdim_gt_numSimples_mul_fpdimProjUnit
    _ ≥ 1 * h.fpdimProjUnit := by
      apply mul_le_mul_of_nonneg_right hN (le_of_lt h.fpdimProjUnit_pos)
    _ = h.fpdimProjUnit := one_mul _

end CategoryTheory

/--
[endo_isIso_of_comp_epi_eq_of_localEnd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FiniteTensorCategory.lean)
-/
@[path]
private lemma endo_isIso_of_comp_epi_eq_of_localEnd_eq
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {P X : C}
  [Projective P]
  [Simple X]
  [IsLocalRing (End P)]
  {π : P ⟶ X}
  [Epi π]
  {f : End P}
-- given
  (hf : f ≫ π = π) :
-- imply
  IsIso f := by
-- proof
  apply CategoryTheory.endo_isIso_of_comp_epi_eq_of_localEnd π f hf

/--
[HasRegularObject.fpDimProjCover_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FiniteTensorCategory.lean)
-/
@[path]
private lemma fpDimProjCover_pos_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [h : HasRegularObject C]
  {i : h.ι} :
-- imply
  h.fpDimProjCover i > 0 := by
-- proof
  apply CategoryTheory.HasRegularObject.fpDimProjCover_pos i

/--
[HasRegularObject.fpdimRegular_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FiniteTensorCategory.lean)
-/
@[path]
private lemma fpdimRegular_eq_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [h : HasRegularObject C] :
-- imply
  HasRegularObject.fpdimRegular (C := C) = ∑ i : h.ι, h.regularCoeff i * h.fpDimProjCover i := by
-- proof
  apply CategoryTheory.HasRegularObject.fpdimRegular_eq

/--
[HasRegularObject.fpdimRegular_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FiniteTensorCategory.lean)
-/
@[path]
private lemma fpdimRegular_pos_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [h : HasRegularObject C] :
-- imply
  HasRegularObject.fpdimRegular (C := C) > 0 := by
-- proof
  apply CategoryTheory.HasRegularObject.fpdimRegular_pos

/--
[fpdimRegular_ne_zero_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FiniteTensorCategory.lean)
-/
@[path]
private lemma fpdimRegular_ne_zero_of_pos_eq
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [HasRegularObject C] :
-- imply
  HasRegularObject.fpdimRegular (C := C) ≠ 0 := by
-- proof
  apply CategoryTheory.fpdimRegular_ne_zero_of_pos


-- created on 2026-10-23
