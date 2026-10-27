import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.AlgebraicCurve.CurveModel
open CategoryTheory AlgebraicGeometry AlgebraicCurve


/-- ported from external source -/
@[path]
private lemma main
  {K : Type u} [Field K]
  {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  {cX : X ⟶ Spec (CommRingCat.of K)}
  {cY : Y ⟶ Spec (CommRingCat.of K)}
  {e : X ≅ Y}
-- given
  (he : e.hom ≫ cY = cX) :
-- imply
  let :=
  (baseToFunctionField cX).toAlgebra
    let := (baseToFunctionField cY).toAlgebra
    Nonempty (X.functionField ≃ₐ[K] Y.functionField) := by
-- proof
    let := (baseToFunctionField cX).toAlgebra
    let := (baseToFunctionField cY).toAlgebra
    have hsurj : Function.Surjective e.hom.base := by
      rw [← Scheme.coe_homeoOfIso]; exact (Scheme.homeoOfIso e).surjective
    have hgen : IsGenericPoint (e.hom.base (genericPoint X)) (Set.univ : Set Y) := by
      have h := (genericPoint_spec X).image (f := e.hom.base) e.hom.continuous
      rwa [Set.image_univ_of_surjective hsurj, closure_univ] at h
    have hinsep : Inseparable (genericPoint Y) (e.hom.base (genericPoint X)) :=
      inseparable_iff_specializes_and.mpr
        ⟨genericPoint_specializes _, hgen.specializes (Set.mem_univ _)⟩
    let iso1 : Y.presheaf.stalk (genericPoint Y) ≅ Y.presheaf.stalk (e.hom.base (genericPoint X)) :=
      Y.presheaf.stalkCongr hinsep
    let iso2 : Y.presheaf.stalk (e.hom.base (genericPoint X)) ≅ X.presheaf.stalk (genericPoint X) :=
      asIso (e.hom.stalkMap (genericPoint X))
    let Φ : Y.functionField ≅ X.functionField := iso1 ≪≫ iso2
    have key : ∀ a : K, Φ.hom (baseToFunctionField cY a) = baseToFunctionField cX a := by
      intro a
      have h1 : Y.presheaf.germ ⊤ (genericPoint Y) trivial ≫ iso1.hom =
          Y.presheaf.germ ⊤ (e.hom.base (genericPoint X)) trivial :=
        Y.presheaf.germ_stalkSpecializes _ (hgen.specializes (Set.mem_univ _))
      have h2 : Y.presheaf.germ ⊤ (e.hom.base (genericPoint X)) trivial ≫ iso2.hom =
          e.hom.app ⊤ ≫ X.presheaf.germ ⊤ (genericPoint X) trivial :=
        Scheme.Hom.germ_stalkMap e.hom ⊤ (genericPoint X) trivial
      have h3 : cX.appTop = cY.appTop ≫ e.hom.appTop := by
        rw [← he]; rfl
      have hΦ : Y.presheaf.germ ⊤ (genericPoint Y) trivial ≫ Φ.hom =
          e.hom.app ⊤ ≫ X.presheaf.germ ⊤ (genericPoint X) trivial := by
        show Y.presheaf.germ ⊤ (genericPoint Y) trivial ≫ (iso1.hom ≫ iso2.hom) = _
        rw [← Category.assoc, h1, h2]
      show (Y.presheaf.germ ⊤ (genericPoint Y) trivial ≫ Φ.hom)
        (cY.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a)) =
        (X.presheaf.germ ⊤ (genericPoint X) trivial) (cX.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a))
      rw [hΦ, h3]
      rfl
    let f : X.functionField ≃+* Y.functionField := Φ.commRingCatIsoToRingEquiv.symm
    refine ⟨AlgEquiv.ofRingEquiv (f := f) (fun a => ?_)⟩
    show Φ.commRingCatIsoToRingEquiv.symm (baseToFunctionField cX a) = baseToFunctionField cY a
    rw [RingEquiv.symm_apply_eq]
    exact (key a).symm


-- created on 2026-10-23
