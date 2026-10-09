import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
[AlgebraicGeometry_isPullback_Spec_map_pushout_inl_right_inr_right](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isPullback_Spec_map_pushout_inl_right_inr_right.lean)
-/
@[path]
private lemma main
  [CommRing R]
  {B B₁ B₂ : Under (CommRingCat.of R)}
  {φ₁ : B ⟶ B₁}
  {φ₂ : B ⟶ B₂} :
-- imply
  IsPullback (Spec.map (pushout.inl φ₁ φ₂).right) (Spec.map (pushout.inr φ₁ φ₂).right)
    (Spec.map φ₁.right) (Spec.map φ₂.right) :=
-- proof
  isPullback_SpecMap_of_isPushout _ _ _ _ ((IsPushout.of_hasPushout φ₁ φ₂).map (Under.forget _))


-- created on 2026-10-03
