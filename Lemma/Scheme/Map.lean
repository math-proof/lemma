import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u u₁ u₂ u₃

private lemma key
  {CZ : Type u₁} {CZ' : Type u₂} {CX : Type u₃}
  [Category CZ] [Category CZ'] [Category CX]
  (Pbt : CZ' ⥤ CZ)
  (Pt : CZ ⥤ CZ')
  (Pι' : CZ' ⥤ CX)
  (P Pι : CZ ⥤ CX)
  (η : 𝟭 CZ' ⟶ Pbt ⋙ Pt)
  (σ : Pt ⋙ Pι' ⟶ P)
  (κ : P ⟶ Pι)
  {M₁ M₁' : CZ'}
  (φ' : M₁ ⟶ M₁')
  {K K' M₂ M₂' : CZ}
  (α : Pbt.obj M₁ ≅ K)
  (β : K ≅ M₂)
  (α' : Pbt.obj M₁' ≅ K')
  (β' : K' ≅ M₂') :
  (Pι'.map (η.app M₁) ≫ σ.app (Pbt.obj M₁) ≫ P.map α.hom ≫ P.map β.hom ≫ κ.app M₂) ≫ Pι.map ((α.trans β).inv ≫ Pbt.map φ' ≫ (α'.trans β').hom) = Pι'.map φ' ≫ (Pι'.map (η.app M₁') ≫ σ.app (Pbt.obj M₁') ≫ P.map α'.hom ≫ P.map β'.hom ≫ κ.app M₂') := by
  simp only [Iso.trans_hom, Iso.trans_inv, Category.assoc]
  rw [← κ.naturality, ← P.map_comp_assoc, ← P.map_comp_assoc]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Functor.map_comp]
  erw [← σ.naturality_assoc]
  simp only [Functor.comp_map]
  have hη : φ' ≫ η.app M₁' = η.app M₁ ≫ Pt.map (Pbt.map φ') := by
    have e := η.naturality φ'
    simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map] at e
    apply e
  erw [← Pι'.map_comp_assoc, ← hη]
  erw [Pι'.map_comp_assoc]

/--
[AlgebraicGeometry_Scheme_Modules_transition_comp_pushforward_map_eq_pushforward_map_comp_transition_of_comp_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_transition_comp_pushforward_map_eq_pushforward_map_comp_transition_of_comp_eq.lean)
-/
@[path]
private lemma main
  {Z Z' X : (Scheme : Type (u + 1))}
  (t : Z ⟶ Z')
  (ι' : Z' ⟶ X)
  (ι : Z ⟶ X)
  (h : t ≫ ι' = ι)
  (N N' : X.Modules)
  (φ' : (Scheme.Modules.pullback ι').obj N ⟶ (Scheme.Modules.pullback ι').obj N')
  (φ : (Scheme.Modules.pullback ι).obj N ⟶ (Scheme.Modules.pullback ι).obj N')
  (hφ : φ = (((Scheme.Modules.pullbackComp t ι').app N).trans ((Scheme.Modules.pullbackCongr h).app N)).inv ≫ (Scheme.Modules.pullback t).map φ' ≫ (((Scheme.Modules.pullbackComp t ι').app N').trans ((Scheme.Modules.pullbackCongr h).app N')).hom) :
  ((Scheme.Modules.pushforward ι').map ((Scheme.Modules.pullbackPushforwardAdjunction t).unit.app ((Scheme.Modules.pullback ι').obj N)) ≫ (Scheme.Modules.pushforwardComp t ι').hom.app ((Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback ι').obj N)) ≫ (Scheme.Modules.pushforward (t ≫ ι')).map ((Scheme.Modules.pullbackComp t ι').hom.app N) ≫ (Scheme.Modules.pushforward (t ≫ ι')).map ((Scheme.Modules.pullbackCongr h).hom.app N) ≫ (Scheme.Modules.pushforwardCongr h).hom.app ((Scheme.Modules.pullback ι).obj N)) ≫ (Scheme.Modules.pushforward ι).map φ = (Scheme.Modules.pushforward ι').map φ' ≫ ((Scheme.Modules.pushforward ι').map ((Scheme.Modules.pullbackPushforwardAdjunction t).unit.app ((Scheme.Modules.pullback ι').obj N')) ≫ (Scheme.Modules.pushforwardComp t ι').hom.app ((Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback ι').obj N')) ≫ (Scheme.Modules.pushforward (t ≫ ι')).map ((Scheme.Modules.pullbackComp t ι').hom.app N') ≫ (Scheme.Modules.pushforward (t ≫ ι')).map ((Scheme.Modules.pullbackCongr h).hom.app N') ≫ (Scheme.Modules.pushforwardCongr h).hom.app ((Scheme.Modules.pullback ι).obj N')) := by
  subst hφ
  apply key (Scheme.Modules.pullback t) (Scheme.Modules.pushforward t) (Scheme.Modules.pushforward ι') (Scheme.Modules.pushforward (t ≫ ι')) (Scheme.Modules.pushforward ι) (Scheme.Modules.pullbackPushforwardAdjunction t).unit (Scheme.Modules.pushforwardComp t ι').hom (Scheme.Modules.pushforwardCongr h).hom φ' ((Scheme.Modules.pullbackComp t ι').app N) ((Scheme.Modules.pullbackCongr h).app N) ((Scheme.Modules.pullbackComp t ι').app N') ((Scheme.Modules.pullbackCongr h).app N')


-- created on 2026-10-20
