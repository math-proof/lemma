import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_AlgebraicGeometry_ModulesTildePullback
open CategoryTheory AlgebraicGeometry Opposite TensorProduct


/--
[AlgebraicGeometry_tilde_pullbackSpecIso_unit](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_tilde_pullbackSpecIso_unit.lean)
-/
@[path]
private lemma main
  {R S : CommRingCat.{u}}
  {φ : R ⟶ S}
  {M : ModuleCat.{u} R} :
-- imply
  ((tilde.adjunction (R :=
  R)).comp
          (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).unit.app M ≫
        (Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R)).map
  (tilde.pullbackSpecIso φ M).hom ≫
    (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.app (tilde ((ModuleCat.extendScalars φ.hom).obj M)) =
      (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M ≫
        (ModuleCat.restrictScalars φ.hom).map
          ((tilde.adjunction (R := S)).unit.app ((ModuleCat.extendScalars φ.hom).obj M)) := by
-- proof
    have h : ((tilde.adjunction (R := R)).comp
          (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).unit.app M ≫
        (Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R)).map
          (tilde.pullbackSpecIso φ M).hom =
        ((((ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := S))).ofNatIsoRight
          (Scheme.Modules.pushforwardSpecCompΓIso φ).symm).unit.app M) :=
      Adjunction.unit_leftAdjointUniq_hom_app _ _ M
    simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
      Iso.symm_hom] at h
    rw [Adjunction.comp_unit_app (ModuleCat.extendRestrictScalarsAdj φ.hom)] at h
    have h2 := congrArg (· ≫ (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.app
      ((ModuleCat.extendScalars φ.hom ⋙ tilde.functor S).obj M)) h
    simp only [Category.assoc, Iso.inv_hom_id_app] at h2
    exact h2


-- created on 2026-10-23
