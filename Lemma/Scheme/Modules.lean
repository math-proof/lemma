import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {X Y Z W : Scheme.{u}}
private lemma sa {V : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ V) : (f ≫ g) ≫ h = f ≫ g ≫ h := rfl
private lemma pullbackCongr_hom_app {f g : X ⟶ Y} (h : f = g) (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr h).hom.app M = eqToHom (by rw [h]) := by
  subst h; simp [Scheme.Modules.pullbackCongr]
private lemma assoc_app (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (M : W.Modules) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app M) ≫
        (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app M =
      (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫
        (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M := by
  have H := congr_app (congr_arg Iso.hom
    (SheafOfModules.pullback_assoc.{u} h.toRingCatSheafHom g.toRingCatSheafHom f.toRingCatSheafHom)) M
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_inv_app] at H
  erw [Category.id_comp] at H
  exact H.symm
private lemma hom_inv_app {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} (e : F ≅ G) (M : C) :
    e.hom.app M ≫ e.inv.app M = 𝟙 _ := by
  rw [← NatTrans.comp_app, Iso.hom_inv_id, NatTrans.id_app]
private lemma inv_hom_app {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} (e : F ≅ G) (M : C) :
    e.inv.app M ≫ e.hom.app M = 𝟙 _ := by
  rw [← NatTrans.comp_app, Iso.inv_hom_id, NatTrans.id_app]
private lemma star1 (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (M : W.Modules) :
    (Scheme.Modules.pullbackComp f g).inv.app ((Scheme.Modules.pullback h).obj M) ≫
        (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app M) =
      (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M ≫
        (Scheme.Modules.pullbackComp f (g ≫ h)).inv.app M := by
  have A := assoc_app f g h M
  have C := hom_inv_app (Scheme.Modules.pullbackComp f (g ≫ h)) M
  have B : (Scheme.Modules.pullbackComp f g).inv.app ((Scheme.Modules.pullback h).obj M) ≫
      ((Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app M) ≫
        (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app M) =
      (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M := by
    erw [A, reassoc_of% (inv_hom_app (Scheme.Modules.pullbackComp f g) ((Scheme.Modules.pullback h).obj M))]
  dsimp only [Functor.comp_obj, sa] at A B C ⊢
  rw [← B]
  simp only [Category.assoc]
  rw [C]
  simp only [Category.comp_id]
private lemma star2 (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (M : W.Modules) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).inv.app M) ≫
        (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) =
      (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app M ≫
        (Scheme.Modules.pullbackComp (f ≫ g) h).inv.app M := by
  have A := assoc_app f g h M
  have C1 := hom_inv_app (Scheme.Modules.pullbackComp (f ≫ g) h) M
  have C2 : (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).inv.app M) ≫
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app M) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, inv_hom_app, CategoryTheory.Functor.map_id]
  have B : (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app M) ≫
      ((Scheme.Modules.pullbackComp f (g ≫ h)).hom.app M ≫ (Scheme.Modules.pullbackComp (f ≫ g) h).inv.app M) =
      (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) := by
    dsimp only [Functor.comp_obj, sa] at A C1 ⊢
    rw [reassoc_of% A, C1]
    try simp only [Category.comp_id]
  dsimp only [Functor.comp_obj, sa] at B C2 ⊢
  rw [← B]
  try simp only [Category.assoc]
  rw [reassoc_of% C2]
private lemma comp_inv_eqToHom_comp_hom (s : X ⟶ Y) {g g' : Y ⟶ Z} (hg : g = g') (L : Z.Modules) :
    (Scheme.Modules.pullbackComp s g).inv.app L ≫
        eqToHom (show (Scheme.Modules.pullback s).obj ((Scheme.Modules.pullback g).obj L) =
          (Scheme.Modules.pullback s).obj ((Scheme.Modules.pullback g').obj L) by rw [hg]) ≫
        (Scheme.Modules.pullbackComp s g').hom.app L =
      eqToHom (by rw [hg]) := by
  subst hg
  erw [eqToHom_refl, Category.id_comp, ← NatTrans.comp_app, Iso.inv_hom_id, NatTrans.id_app]
  exact (eqToHom_refl _ _).symm
private lemma eqToHom_comp_hom (a : Y ⟶ Z) {f f' : X ⟶ Y} (hf : f = f') (L : Z.Modules) :
    eqToHom (show (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback a).obj L) =
        (Scheme.Modules.pullback f').obj ((Scheme.Modules.pullback a).obj L) by rw [hf]) ≫
        (Scheme.Modules.pullbackComp f' a).hom.app L =
      (Scheme.Modules.pullbackComp f a).hom.app L ≫ eqToHom (by rw [hf]) := by
  subst hf; simp
/--
[AlgebraicGeometry_Scheme_Modules_pullback_mapIso_pullbackComp_app_trans_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_pullback_mapIso_pullbackComp_app_trans_eq.lean)
-/
@[path]
private lemma main
    {T₃ T₂ T₁ X₃ A'' A' : Scheme.{u}} (e₃ : T₃ ⟶ X₃) (b : X₃ ⟶ A'') (s : T₃ ⟶ T₂) (e'' : T₂ ⟶ A'')
    (a : A'' ⟶ A') (i : T₂ ⟶ T₁) (e' : T₁ ⟶ A') (hb : e₃ ≫ b = s ≫ e'') (ha : e'' ≫ a = i ≫ e')
    (hk : e₃ ≫ b ≫ a = (s ≫ i) ≫ e') (L : A'.Modules) :
    (Scheme.Modules.pullback e₃).mapIso ((Scheme.Modules.pullbackComp b a).app L) ≪≫
        ((Scheme.Modules.pullbackComp e₃ (b ≫ a)).app L ≪≫ (Scheme.Modules.pullbackCongr hk).app L ≪≫
          ((Scheme.Modules.pullbackComp (s ≫ i) e').app L).symm) =
      ((Scheme.Modules.pullbackComp e₃ b).app ((Scheme.Modules.pullback a).obj L) ≪≫
          (Scheme.Modules.pullbackCongr hb).app ((Scheme.Modules.pullback a).obj L) ≪≫
          ((Scheme.Modules.pullbackComp s e'').app ((Scheme.Modules.pullback a).obj L)).symm) ≪≫
        (Scheme.Modules.pullback s).mapIso
          ((Scheme.Modules.pullbackComp e'' a).app L ≪≫ (Scheme.Modules.pullbackCongr ha).app L ≪≫
            ((Scheme.Modules.pullbackComp i e').app L).symm) ≪≫
        (Scheme.Modules.pullbackComp s i).app ((Scheme.Modules.pullback e').obj L) := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, Functor.map_comp,
    Category.assoc, pullbackCongr_hom_app, eqToHom_map]
  have h1 := assoc_app e₃ b a L
  have h2 := star1 s e'' a L
  have h3 := star2 s i e' L
  have h4 := comp_inv_eqToHom_comp_hom s ha L
  have h5 := eqToHom_comp_hom a hb L
  dsimp only [Functor.comp_obj, sa] at h1 h2 h3 h4 h5 ⊢
  rw [reassoc_of% h1, reassoc_of% h2, h3, reassoc_of% h4, reassoc_of% h5]
  simp only [eqToHom_trans_assoc]

-- created on 2026-10-20
