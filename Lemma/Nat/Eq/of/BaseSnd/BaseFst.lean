import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
[AlgebraicGeometry_Scheme_Pullback_eq_of_fst_eq_of_snd_eq_of_isIso_residueFieldMap](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Pullback_eq_of_fst_eq_of_snd_eq_of_isIso_residueFieldMap.lean)
-/
@[main]
private lemma main
  {X Y S : Scheme.{u}}
  {f : X ⟶ S}
  {g : Y ⟶ S}
  {t₁ t₂ : ↥(pullback f g)} [IsIso (f.residueFieldMap ((pullback.fst f g).base t₂))]
-- given
  (h₁ : (pullback.fst f g).base t₁ = (pullback.fst f g).base t₂)
  (h₂ : (pullback.snd f g).base t₁ = (pullback.snd f g).base t₂) :
-- imply
  t₁ = t₂ := by
-- proof
  apply Scheme.Pullback.carrierEquiv.injective
  refine Scheme.Pullback.carrierEquiv_eq_iff.mpr ⟨Scheme.Pullback.Triplet.ext h₁ h₂, ?_⟩

  set T := Scheme.Pullback.Triplet.ofPoint t₂ with hT
  haveI : IsIso ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x) := by
    haveI : IsIso (f.residueFieldMap T.x) := inferInstanceAs (IsIso (f.residueFieldMap ((pullback.fst f g).base t₂)))
    infer_instance
  haveI hinr : IsIso (pushout.inr ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)
      ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y)) :=
    pushout_inr_iso_of_left_iso _ _
  have hsub : Subsingleton ↥(Spec T.tensor) := by
    constructor
    intro a b
    exact (Spec.map (pushout.inr ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)
      ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y))).isOpenEmbedding.injective (Subsingleton.elim _ _)
  exact @Subsingleton.elim _ hsub _ _


-- created on 2026-10-05
