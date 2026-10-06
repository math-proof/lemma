import Mathlib
import sympy.Basic

open CategoryTheory AlgebraicGeometry

/--
[AlgebraicGeometry_existsUnique_section_comp_eq_of_universallyClosed_of_isSeparated](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_existsUnique_section_comp_eq_of_universallyClosed_of_isSeparated.lean)
-/
@[main]
private lemma main
  {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
  {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
  {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of R)} [UniversallyClosed f] [IsSeparated f]
  {x : Spec (CommRingCat.of K) ⟶ X}
-- given
  (hx : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R K))) :
-- imply
  ∃! σ : Spec (CommRingCat.of R) ⟶ X,
      σ ≫ f = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ σ = x := by
-- proof
  let S : ValuativeCommSq f := ValuativeCommSq.mk R K x (𝟙 _) ⟨by rw [Category.comp_id]; exact hx⟩
  have hE : S.commSq.HasLift := by
    have h := UniversallyClosed.eq_valuativeCriterion
    have : (ValuativeCriterion.Existence ⊓ @QuasiCompact) f := h ▸ (inferInstance : UniversallyClosed f)
    exact this.1 S
  have hU : Subsingleton S.commSq.LiftStruct := IsSeparated.valuativeCriterion f S
  refine ⟨S.commSq.lift, ⟨S.commSq.fac_right, S.commSq.fac_left⟩, ?_⟩
  rintro σ ⟨h1, h2⟩
  let l₁ : S.commSq.LiftStruct := ⟨σ, h2, h1⟩
  let l₂ : S.commSq.LiftStruct := ⟨S.commSq.lift, S.commSq.fac_left, S.commSq.fac_right⟩
  exact congrArg CommSq.LiftStruct.l (Subsingleton.elim l₁ l₂)


-- created on 2026-10-05
