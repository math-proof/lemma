import Mathlib
import sympy.Basic
import Class.v1.Atlas.TensorCategories.code.UnitProjective
open CategoryTheory MonoidalCategory Limits TensorCategories


namespace TensorCategories

/--
[Proposition_1_13_6](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitProjective.lean)
-/
@[path]
lemma Proposition_1_13_6
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  {P X : C}
  [hP : Projective P]
  [hX : HasRightDual X]
-- given
  (whiskerRight_epi : ∀ {A B : C} (f : A ⟶ B) [Epi f] (Z : C), Epi (f ▷ Z)) :
-- imply
  Projective (P ⊗ X) where factors := by
-- proof
  intro E Y f e he
  let f' : P ⟶ Y ⊗ Xᘁ := (tensorRightHomEquiv P X (Xᘁ) Y) f
  have he' : Epi (e ▷ Xᘁ) := whiskerRight_epi e (Xᘁ)
  obtain ⟨g', hg'⟩ := Projective.factors f' (e ▷ Xᘁ)
  use (tensorRightHomEquiv P X (Xᘁ) E).symm g'
  apply (tensorRightHomEquiv P X (Xᘁ) Y).injective
  rw [tensorRightHomEquiv_naturality]
  change (tensorRightHomEquiv P X (Xᘁ) E) ((tensorRightHomEquiv P X (Xᘁ) E).symm g') ≫
    e ▷ Xᘁ = f'
  rwa [Equiv.apply_symm_apply]

end TensorCategories

namespace TensorCategories

/--
[epi_section_of_biproduct_simples](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitProjective.lean)
-/
@[path]
lemma epi_section_of_biproduct_simples
  {C : Type u}
  [Category.{v} C]
  [Preadditive C]
  [Abelian C]
  {S : C}
  [Simple S]
  {n : ℕ}
  {W : Fin n → C}
  [HasBiproduct W]
  {e : (⨁ W) ⟶ S}
  [Epi e]
-- given
  (hW : ∀ j, Simple (W j)) :
-- imply
  ∃ s : S ⟶ ⨁ W, s ≫ e = 𝟙 S := by
-- proof
  have he_ne : e ≠ 0 := by
    intro he
    apply Simple.not_isZero S
    rw [IsZero.iff_id_eq_zero]
    subst he
    exact (cancel_epi (0 : (⨁ W) ⟶ S)).mp (by simp)
  have ⟨j, hj⟩ : ∃ j, biproduct.ι W j ≫ e ≠ 0 := by
    by_contra h
    push Not at h
    apply he_ne
    ext k
    simp [h k]
  haveI := hW j
  haveI : IsIso (biproduct.ι W j ≫ e) := isIso_of_hom_simple hj
  exact ⟨inv (biproduct.ι W j ≫ e) ≫ biproduct.ι W j,
    by rw [Category.assoc, IsIso.inv_hom_id]⟩

end TensorCategories

namespace TensorCategories

/--
[simple_projective_of_semisimple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitProjective.lean)
-/
@[path]
lemma simple_projective_of_semisimple
  {C : Type u}
  [Category.{v} C]
  [Preadditive C]
  [Abelian C]
  [IsSemisimpleCategory C]
  {S : C}
  [Simple S] :
-- imply
  Projective S := by
-- proof
  constructor
  intro E Y f e he
  obtain ⟨n, W, hW, hbp, ⟨φ⟩⟩ := IsSemisimpleCategory.semisimple (C := C) (pullback f e)
  haveI := hbp
  haveI : Epi (pullback.fst f e) := Abelian.epi_pullback_of_epi_g f e
  haveI : Epi (φ.inv ≫ pullback.fst f e) := epi_comp _ _
  obtain ⟨s, hs⟩ := epi_section_of_biproduct_simples S W hW (φ.inv ≫ pullback.fst f e)
  refine ⟨s ≫ φ.inv ≫ pullback.snd f e, ?_⟩
  have cond : pullback.snd f e ≫ e = pullback.fst f e ≫ f := pullback.condition.symm
  rw [Category.assoc, Category.assoc, cond, ← Category.assoc (φ.inv), ← Category.assoc s, hs]
  simp

end TensorCategories

namespace TensorCategories

/--
[biproduct_projective_of_components](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitProjective.lean)
-/
@[path]
lemma biproduct_projective_of_components
  {C : Type u}
  [Category.{v} C]
  [Preadditive C]
  {n : ℕ}
  {Y : Fin n → C}
  [HasBiproduct Y]
-- given
  (hP : ∀ i, Projective (Y i)) :
-- imply
  Projective (⨁ Y) := by
-- proof
  constructor
  intro E X f e he
  have lift : ∀ i, ∃ g : Y i ⟶ E, g ≫ e = biproduct.ι Y i ≫ f := by
    intro i; exact (hP i).factors (biproduct.ι Y i ≫ f) e
  choose g hg using lift
  exact ⟨biproduct.desc g, by ext i; simp [hg i]⟩

end TensorCategories

namespace TensorCategories

/--
[semisimple_implies_projective'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitProjective.lean)
-/
@[path]
lemma semisimple_implies_projective'
  {C : Type u}
  [Category.{v} C]
  [Preadditive C]
  [Abelian C]
  [MonoidalCategory C]
  [MonoidalPreadditive C]
  [IsSemisimpleCategory C]
  {X : C} :
-- imply
  Projective X := by
-- proof
  obtain ⟨n, Y, hY, hbp, ⟨φ⟩⟩ := IsSemisimpleCategory.semisimple (C := C) X
  haveI := hbp
  have hProj : ∀ i, Projective (Y i) := fun i => by
    haveI := hY i; exact simple_projective_of_semisimple (Y i)
  have hBP : Projective (⨁ Y) := biproduct_projective_of_components Y hProj
  constructor
  intro E Z f e he
  obtain ⟨g', hg'⟩ := hBP.factors (φ.inv ≫ f) e
  exact ⟨φ.hom ≫ g', by
    rw [Category.assoc, hg', ← Category.assoc, φ.hom_inv_id, Category.id_comp]⟩
/-- Converse direction: in a finite-length abelian category, if every object is
projective then the category is semisimple. -/
section Cor_1_13_7
variable (k : Type*) [Field k]
variable (C : Type u) [Category.{v} C]
  [Preadditive C] [Linear k C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]

end TensorCategories

namespace TensorCategories

/--
[Corollary_1_13_7](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitProjective.lean)
-/
@[path]
lemma Corollary_1_13_7
  {k : Type*}
  [Field k]
  {C : Type u}
  [Category.{v} C]
  [hMR : MultiringCategory k C]
  [∀ (X : C), HasRightDual X] :
-- imply
  Projective (𝟙_ C) ↔ IsSemisimpleCategory C := by
-- proof
  constructor
  ·
    intro hProj
    apply allProjective_implies_semisimple' (hfl := hMR.toLocallyFiniteCategory.hasFiniteLength)
    intro X
    have h1 : Projective (𝟙_ C ⊗ X) :=
      Proposition_1_13_6 hMR.whiskerRight_epi
    exact Projective.of_iso (λ_ X) h1
  ·
    intro hSS
    exact semisimple_implies_projective' (𝟙_ C)

end TensorCategories


-- created on 2026-10-23
