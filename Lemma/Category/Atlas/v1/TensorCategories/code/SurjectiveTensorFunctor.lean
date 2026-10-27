import Mathlib
import Initialize.Tactic.Attr.Basic
import Class.v1.Atlas.TensorCategories.code.SurjectiveTensorFunctor
open CategoryTheory CategoryTheory.Limits MonoidalCategory


/--
[projective_is_injective_in_finite_tensor_category](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SurjectiveTensorFunctor.lean)
-/
@[path]
lemma projective_is_injective_in_finite_tensor_category
  {D : Type u₁}
  [Category.{v₁} D]
  [ProjectiveIsInjective D]
  {Q : D}
-- given
  (hQ : Projective Q) :
-- imply
  Injective Q :=
-- proof
  ProjectiveIsInjective.injective_of_projective Q hQ

/--
[isZero_of_no_nonzero_projective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SurjectiveTensorFunctor.lean)
-/
@[path]
lemma isZero_of_no_nonzero_projective
  {D : Type u₁}
  [Category.{v₁} D]
  [Abelian D]
  [EnoughProjectives D]
  {X : D}
-- given
  (h : ∀ (Q : D), Projective Q → IsZero Q) :
-- imply
  IsZero X :=
-- proof
  IsZero.of_epi (Projective.π X) (h _ (Projective.projective_over X))


-- created on 2026-10-23
