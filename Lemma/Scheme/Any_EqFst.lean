import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_exists_algEquiv_globalSections_pullback_spec_tensorProduct](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_algEquiv_globalSections_pullback_spec_tensorProduct.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] {X : (Scheme : Type (u + 1))} (f : X ⟶ Spec (CommRingCat.of R)) [IsAffine X]
  (S : Type u) [CommRing S] [Algebra R S] :
    let _ : Algebra R (X.presheaf.obj (op ⊤)) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom.toAlgebra
    let _ : Algebra S ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap R S)))).presheaf.obj (op ⊤)) := ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R S)))).appTop).hom.toAlgebra
    ∃ e : AlgEquiv S (TensorProduct R S (X.presheaf.obj (op ⊤))) ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap R S)))).presheaf.obj (op ⊤)), ∀ a : X.presheaf.obj (op ⊤), e (TensorProduct.tmul R (1 : S) a) = (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R S)))).appTop a := by
  classical
  set g := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let _ : Algebra R (X.presheaf.obj (op ⊤)) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom.toAlgebra
  let _ : Algebra S ((pullback f g).presheaf.obj (op ⊤)) := ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ (pullback.snd f g).appTop).hom.toAlgebra
  set φ : CommRingCat.of R ⟶ X.presheaf.obj (op ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop with hφ
  have hφ' : CommRingCat.ofHom (algebraMap R (X.presheaf.obj (op ⊤))) = φ := by
    rw [hφ]
    rfl
  set f₀ : Spec (X.presheaf.obj (op ⊤)) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R (X.presheaf.obj (op ⊤)))) with hf₀
  have hf : f = X.isoSpec.hom ≫ f₀ := by
    have h1 := Scheme.isoSpec_hom_naturality f
    have h2 : (Spec (CommRingCat.of R)).isoSpec.hom = Spec.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
      rw [Scheme.isoSpec_hom, SpecMap_ΓSpecIso_hom]
    rw [h2] at h1
    rw [hf₀, hφ', hφ, Spec.map_comp, ← Category.assoc, h1, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  let ε : pullback f g ≅ Spec (CommRingCat.of (TensorProduct R (X.presheaf.obj (op ⊤)) S)) :=
    (asIso (pullback.map f g f₀ g X.isoSpec.hom (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hf]) (by rw [Category.comp_id, Category.id_comp]))).trans (pullbackSpecIso R (X.presheaf.obj (op ⊤)) S)
  have hε_fst : ε.hom ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) = pullback.fst f g ≫ X.isoSpec.hom := by
    simp only [ε, Iso.trans_hom, asIso_hom, Category.assoc]
    rw [show (pullbackSpecIso R (X.presheaf.obj (op ⊤)) S).hom ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : RingHom (X.presheaf.obj (op ⊤)) (TensorProduct R (X.presheaf.obj (op ⊤)) S))) = pullback.fst f₀ g from pullbackSpecIso_hom_fst R (X.presheaf.obj (op ⊤)) S, pullback.lift_fst]
  have hε_snd : ε.hom ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : RingHom S (TensorProduct R (X.presheaf.obj (op ⊤)) S))) = pullback.snd f g := by
    have h0 := pullbackSpecIso_hom_snd R (X.presheaf.obj (op ⊤)) S
    simp only [ε, Iso.trans_hom, asIso_hom, Category.assoc]
    rw [show (pullbackSpecIso R (X.presheaf.obj (op ⊤)) S).hom ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : RingHom S (TensorProduct R (X.presheaf.obj (op ⊤)) S))) = pullback.snd f₀ g from h0, pullback.lift_snd, Category.comp_id]
  let Ψ : CommRingCat.of (TensorProduct R (X.presheaf.obj (op ⊤)) S) ≅ (pullback f g).presheaf.obj (op ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of (TensorProduct R (X.presheaf.obj (op ⊤)) S))).symm).trans (Scheme.Γ.mapIso ε.op)
  have hΨ : Ψ.hom = (Scheme.ΓSpecIso (CommRingCat.of (TensorProduct R (X.presheaf.obj (op ⊤)) S))).inv ≫ ε.hom.appTop := rfl
  have hΨ_left : CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ Ψ.hom = (pullback.fst f g).appTop := by
    have h := congrArg Scheme.Hom.appTop hε_fst
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop] at h
    have hn := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : RingHom (X.presheaf.obj (op ⊤)) (TensorProduct R (X.presheaf.obj (op ⊤)) S)))
    rw [hΨ, ← Category.assoc, hn, Category.assoc, h, ← Category.assoc]
    show ((Scheme.ΓSpecIso (X.presheaf.obj (op ⊤))).inv ≫ (Scheme.ΓSpecIso (X.presheaf.obj (op ⊤))).hom) ≫ _ = _
    rw [Iso.inv_hom_id, Category.id_comp]
  have hΨ_right : CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : RingHom S (TensorProduct R (X.presheaf.obj (op ⊤)) S)) ≫ Ψ.hom = (Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ (pullback.snd f g).appTop := by
    have h := congrArg Scheme.Hom.appTop hε_snd
    rw [Scheme.Hom.comp_appTop] at h
    have hn := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : RingHom S (TensorProduct R (X.presheaf.obj (op ⊤)) S)))
    rw [hΨ, ← Category.assoc, hn, Category.assoc, h]
  let ΨE : RingEquiv (TensorProduct R (X.presheaf.obj (op ⊤)) S) ((pullback f g).presheaf.obj (op ⊤)) := Ψ.commRingCatIsoToRingEquiv
  let E : RingEquiv (TensorProduct R S (X.presheaf.obj (op ⊤))) ((pullback f g).presheaf.obj (op ⊤)) :=
    ((Algebra.TensorProduct.comm R S (X.presheaf.obj (op ⊤))).toRingEquiv).trans ΨE
  have hE : ∀ (s : S) (a : X.presheaf.obj (op ⊤)), E (TensorProduct.tmul R s a) = Ψ.hom (TensorProduct.tmul R a s) := fun _ _ => rfl
  have hleft : ∀ a : X.presheaf.obj (op ⊤), Ψ.hom (TensorProduct.tmul R a (1 : S)) = (pullback.fst f g).appTop a := by
    intro a
    have happ := RingHom.congr_fun (CommRingCat.hom_ext_iff.mp hΨ_left) a
    rw [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
      Algebra.TensorProduct.includeLeftRingHom_apply] at happ
    apply happ
  have hright : ∀ s : S, Ψ.hom (TensorProduct.tmul R (1 : X.presheaf.obj (op ⊤)) s) = algebraMap S ((pullback f g).presheaf.obj (op ⊤)) s := by
    intro s
    have happ := RingHom.congr_fun (CommRingCat.hom_ext_iff.mp hΨ_right) s
    nth_rw 1 [CommRingCat.hom_comp] at happ
    rw [RingHom.comp_apply, CommRingCat.hom_ofHom, AlgHom.toRingHom_eq_coe] at happ
    rw [AlgHom.coe_toRingHom Algebra.TensorProduct.includeRight,
      Algebra.TensorProduct.includeRight_apply] at happ
    apply happ
  refine ⟨AlgEquiv.ofRingEquiv (f := E) (fun s => ?_), fun a => ?_⟩
  · rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, hE, hright]
  ·
    show E (TensorProduct.tmul R (1 : S) a) = _
    rw [hE, hleft]


-- created on 2026-10-20
