import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.QuasiTensorFunctorProjective
open CategoryTheory CategoryTheory.Limits MonoidalCategory


namespace CategoryTheory

/--
[Projective.of_retract_categorical](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuasiTensorFunctorProjective.lean)
-/
@[path]
lemma Projective.of_retract_categorical
  {C : Type u}
  [Category.{v} C]
  {Q Y : C}
  {i : Q ⟶ Y}
  {r : Y ⟶ Q}
  [hY : Projective Y]
-- given
  (hir : i ≫ r = 𝟙 Q) :
-- imply
  Projective Q where factors := by
-- proof
  intro E X f e he
  haveI := he
  obtain ⟨h', hh'⟩ := Projective.factors (r ≫ f) e
  exact ⟨i ≫ h', by rw [Category.assoc, hh', ← Category.assoc, hir, Category.id_comp]⟩

end CategoryTheory

namespace CategoryTheory

/--
[exists_nonzero_projective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuasiTensorFunctorProjective.lean)
-/
@[path]
lemma exists_nonzero_projective
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Abelian C]
  [EnoughProjectives C]
  [HasNonZeroUnit C] :
-- imply
  ∃ (Q : C), Projective Q ∧ ¬IsZero Q := by
-- proof
  refine ⟨Projective.over (𝟙_ C), Projective.projective_over _, ?_⟩
  intro hZ
  apply HasNonZeroUnit.unit_nonzero (C := C)
  rw [IsZero.iff_id_eq_zero]
  have hπ : Projective.π (𝟙_ C) = 0 := hZ.eq_of_src _ _
  rw [← cancel_epi (Projective.π (𝟙_ C)), hπ, zero_comp, comp_zero]

end CategoryTheory

namespace CategoryTheory

/--
[covers_proj_by_proj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuasiTensorFunctorProjective.lean)
-/
@[path]
lemma covers_proj_by_proj
  {k : Type w}
  [Field k]
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Abelian C]
  [EnoughProjectives C]
  {D : Type u₁}
  [Category.{v₁} D]
  [MonoidalCategory D]
  [Abelian D]
  [ProjectiveIsInjective D]
  {QTF : SurjectiveQuasiTensorFunctor k C D}
  {Q : D}
-- given
  (hQ_proj : Projective Q)
  (_hQ_nz : ¬IsZero Q) :
-- imply
  ∃ (P : C), Projective P ∧ IsRetractOf Q (QTF.F.obj P) := by
-- proof
  haveI := QTF.surjective
  haveI := QTF.preservesMono
  haveI := QTF.preservesEpi
  obtain ⟨X, A, m, e, hm, he⟩ := Functor.IsSurjective.surj (F := QTF.F) Q
  haveI := hm; haveI := he
  set P := Projective.over X
  set π := Projective.π X
  haveI : Projective P := Projective.projective_over X
  haveI : Epi π := Projective.π_epi X
  have hFπ_epi : Epi (QTF.F.map π) := inferInstance
  haveI := hQ_proj
  haveI : Injective Q := ProjectiveIsInjective.injective_of_projective Q hQ_proj
  obtain ⟨s, hs⟩ := Projective.factors (𝟙 Q) e
  obtain ⟨t, ht⟩ := Projective.factors (s ≫ m) (QTF.F.map π)
  haveI : Mono s := (SplitMono.mk e hs).mono
  haveI : Mono (s ≫ m) := mono_comp s m
  have htMono : Mono t := by
    constructor
    intro Z f g h
    have h1 : f ≫ (s ≫ m) = g ≫ (s ≫ m) := by
      rw [← ht]
      simp only [← Category.assoc]
      rw [h]
    exact (cancel_mono (s ≫ m)).mp h1
  haveI := htMono
  obtain ⟨r, hr⟩ := Injective.factors (𝟙 Q) t
  exact ⟨P, Projective.projective_over X, t, r, hr⟩

end CategoryTheory

namespace CategoryTheory

/--
[defectDichotomy_not_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuasiTensorFunctorProjective.lean)
-/
@[path]
lemma defectDichotomy_not_right
  {k : Type w}
  [Field k]
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Abelian C]
  [EnoughProjectives C]
  {D : Type u₁}
  [Category.{v₁} D]
  [MonoidalCategory D]
  [Abelian D]
  [ProjectiveIsInjective D]
  {QTF : SurjectiveQuasiTensorFunctor k C D}
-- given
  (hD_nontrivial : ∃ (Q : D), Projective Q ∧ ¬IsZero Q) :
-- imply
  ¬(∀ (P : C), Projective P → ∀ (Q : D), Projective Q → ¬IsZero Q → ¬IsRetractOf Q (QTF.F.obj P)) := by
-- proof
  intro h_no_summand
  obtain ⟨Q, hQ_proj, hQ_nz⟩ := hD_nontrivial
  obtain ⟨P', hP'_proj, hRetract⟩ := covers_proj_by_proj QTF Q hQ_proj hQ_nz
  exact h_no_summand P' hP'_proj Q hQ_proj hQ_nz hRetract
/-- A surjective quasi-tensor functor into a target category with a nonzero
projective object (and where projectives are injective) preserves projectives. -/

end CategoryTheory


-- created on 2026-10-23
