import Mathlib
import sympy.Basic

open CategoryTheory AlgebraicGeometry

/--
[AlgebraicGeometry_IsSeparated_eq_of_spec_map_subtype_comp_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_IsSeparated_eq_of_spec_map_subtype_comp_eq.lean)
-/
@[path]
private lemma main
  [Field Ω]
  {X Y : Scheme.{0}}
  {f : X ⟶ Y} [IsSeparated f]
  {A : ValuationSubring Ω}
  {s₁ s₂ : Spec (CommRingCat.of ↥A) ⟶ X}
-- given
  (h : Spec.map (CommRingCat.ofHom A.subtype) ≫ s₁ = Spec.map (CommRingCat.ofHom A.subtype) ≫ s₂)
  (hf : s₁ ≫ f = s₂ ≫ f) :
-- imply
  s₁ = s₂ := by
-- proof
  have hA : CommRingCat.ofHom A.subtype = CommRingCat.ofHom (algebraMap (↥A) Ω) := rfl
  let S : ValuativeCommSq f :=
    { R := ↥A
      K := Ω
      i₁ := Spec.map (CommRingCat.ofHom (algebraMap (↥A) Ω)) ≫ s₁
      i₂ := s₁ ≫ f
      commSq := ⟨by rw [Category.assoc]⟩ }
  have hsub : Subsingleton S.commSq.LiftStruct := IsSeparated.valuativeCriterion f S
  let l₁ : S.commSq.LiftStruct := ⟨s₁, rfl, rfl⟩
  let l₂ : S.commSq.LiftStruct := ⟨s₂, by rw [← hA]; exact h.symm, hf.symm⟩
  have := hsub.elim l₁ l₂
  exact congrArg CommSq.LiftStruct.l this


-- created on 2026-10-05
