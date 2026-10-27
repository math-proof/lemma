import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.TensorCategories.code.Corollary_1_15_9
open CategoryTheory MonoidalCategory Limits


/--
[coevaluation_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Corollary_1_15_9.lean)
-/
@[path]
lemma coevaluation_ne_zero
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Abelian C]
  {X : C}
-- given
  (hX : ¬ IsZero X) :
-- imply
  η_ X (Xᘁ) ≠ 0 := by
-- proof
  intro h
  apply hX
  rw [IsZero.iff_id_eq_zero]
  have triangle := ExactPairing.evaluation_coevaluation X (Xᘁ)
  rw [h, MonoidalPreadditive.zero_whiskerRight] at triangle
  simp only [zero_comp] at triangle
  have heq : (λ_ X).hom ≫ (ρ_ X).inv = 0 := triangle.symm
  have h1 : (ρ_ X).inv = 0 := by
    have := congr_arg ((λ_ X).inv ≫ ·) heq
    simp only [Iso.inv_hom_id_assoc, comp_zero] at this
    exact this
  calc 𝟙 X = (ρ_ X).inv ≫ (ρ_ X).hom := by simp
    _ = 0 ≫ (ρ_ X).hom := by rw [h1]
    _ = 0 := by simp

/--
[evaluation_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Corollary_1_15_9.lean)
-/
@[path]
lemma evaluation_ne_zero
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Abelian C]
  {X : C}
-- given
  (hX : ¬ IsZero X) :
-- imply
  ε_ X (Xᘁ) ≠ 0 := by
-- proof
  intro h
  apply hX
  rw [IsZero.iff_id_eq_zero]
  have triangle := ExactPairing.evaluation_coevaluation X (Xᘁ)
  rw [h, MonoidalPreadditive.whiskerLeft_zero] at triangle
  simp only [comp_zero] at triangle
  have heq : (λ_ X).hom ≫ (ρ_ X).inv = 0 := triangle.symm
  have h1 : (ρ_ X).inv = 0 := by
    have := congr_arg ((λ_ X).inv ≫ ·) heq
    simp only [Iso.inv_hom_id_assoc, comp_zero] at this
    exact this
  calc 𝟙 X = (ρ_ X).inv ≫ (ρ_ X).hom := by simp
    _ = 0 ≫ (ρ_ X).hom := by rw [h1]
    _ = 0 := by simp
variable [Simple (𝟙_ C)]

/--
[Corollary_1_15_9_evaluation_epi](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Corollary_1_15_9.lean)
-/
@[path]
lemma Corollary_1_15_9_evaluation_epi
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Abelian C]
  [Simple (𝟙_ C)]
  {X : C}
-- given
  (hX : ¬ IsZero X) :
-- imply
  Epi (ε_ X (Xᘁ)) :=
-- proof
  epi_of_nonzero_to_simple (evaluation_ne_zero C hX)

/--
[Corollary_1_15_9_coevaluation_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Corollary_1_15_9.lean)
-/
@[path]
lemma Corollary_1_15_9_coevaluation_mono
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Abelian C]
  [Simple (𝟙_ C)]
  {X : C}
-- given
  (hX : ¬ IsZero X) :
-- imply
  Mono (η_ X (Xᘁ)) :=
-- proof
  mono_of_nonzero_from_simple (coevaluation_ne_zero C hX)

/--
[Corollary_1_15_9](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Corollary_1_15_9.lean)
-/
@[path]
lemma Corollary_1_15_9
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Abelian C]
  [Simple (𝟙_ C)]
  {X : C}
-- given
  (hX : ¬ IsZero X) :
-- imply
  Epi (ε_ X (Xᘁ)) ∧ Mono (η_ X (Xᘁ)) :=
-- proof
  ⟨Corollary_1_15_9_evaluation_epi C hX, Corollary_1_15_9_coevaluation_mono C hX⟩


-- created on 2026-10-23
