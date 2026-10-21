import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma appLE_top {X Y : (Scheme : Type (u + 1))} (f : X ⟶ Y) (e : (⊤ : X.Opens) ≤ ((TopologicalSpace.Opens.map f.base).obj ⊤)) : f.appLE ⊤ ⊤ e = f.appTop :=
  (Scheme.Hom.app_eq_appLE f).symm
private lemma isAffineOpen_V
  {R : Type u} [CommRing R] {X : (Scheme : Type (u + 1))} (f : X ⟶ Spec (CommRingCat.of R))
  (C : Type u) [CommRing C] [Algebra R C] (ι : Spec (CommRingCat.of C) ⟶ X) [IsOpenImmersion ι]
  (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R C)))
  {A : Type u} [CommRing A] (φ : R →+* A) :
  IsAffineOpen (((TopologicalSpace.Opens.map (pullback.fst f (Spec.map (CommRingCat.ofHom φ))).base).obj ((Scheme.Hom.opensFunctor ι).obj ⊤))) := by
  let _ : Algebra R A := φ.toAlgebra
  let _ : IsAffine (pullback (Spec.map (CommRingCat.ofHom (algebraMap R C))) (Spec.map (CommRingCat.ofHom (algebraMap R A)))) :=
    IsAffine.of_isIso (pullbackSpecIso R C A).hom
  have hφ : Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom (algebraMap R A)) := rfl
  let _ : IsAffine (pullback (ι ≫ f) (Spec.map (CommRingCat.ofHom φ))) :=
    IsAffine.of_isIso (pullback.congrHom hι hφ).hom
  let _ : IsAffine (pullback ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))) :=
    IsAffine.of_isIso (pullbackRightPullbackFstIso f (Spec.map (CommRingCat.ofHom φ)) ι).hom
  have h := isAffineOpen_opensRange (pullback.snd ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ))))
  rwa [Scheme.Hom.opensRange_pullbackSnd, ← Scheme.Hom.image_top_eq_opensRange] at h
private lemma closure_eq_top
  {R : Type u} [CommRing R] {X : (Scheme : Type (u + 1))} (f : X ⟶ Spec (CommRingCat.of R))
  (C : Type u) [CommRing C] [Algebra R C] (ι : Spec (CommRingCat.of C) ⟶ X) [IsOpenImmersion ι]
  (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R C)))
  {A : Type u} [CommRing A] (φ : R →+* A) :
  Subring.closure (Set.range (fun b : C => ((pullback.fst f (Spec.map (CommRingCat.ofHom φ))).app ((Scheme.Hom.opensFunctor ι).obj ⊤)).hom
            ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of C)).inv b))) ∪
         Set.range (fun a : A => ((pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf.map
            (homOfLE (le_top : ((TopologicalSpace.Opens.map (pullback.fst f (Spec.map (CommRingCat.ofHom φ))).base).obj ((Scheme.Hom.opensFunctor ι).obj ⊤)) ≤ ⊤)).op).hom
            ((pullback.snd f (Spec.map (CommRingCat.ofHom φ))).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)))) = ⊤ := by
  classical
  let _ : Algebra R A := φ.toAlgebra
  have hcond : (pullback.fst ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))) ≫ ι = (pullback.snd ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))) ≫ (pullback.fst f (Spec.map (CommRingCat.ofHom φ))) := pullback.condition
  have hφ : (Spec.map (CommRingCat.ofHom φ)) = Spec.map (CommRingCat.ofHom (algebraMap R A)) := rfl
  let E : (pullback ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))) ≅ Spec (.of (TensorProduct R C A)) :=
    (pullbackRightPullbackFstIso f (Spec.map (CommRingCat.ofHom φ)) ι).trans ((pullback.congrHom hι hφ).trans (pullbackSpecIso R C A))
  have hE1 : E.hom ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : C →+* (TensorProduct R C A))) = (pullback.fst ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))) := by
    simp only [E, Iso.trans_hom, Category.assoc, pullbackSpecIso_hom_fst, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id, pullbackRightPullbackFstIso_hom_fst]
  have hE2 : E.hom ≫ Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight : A →ₐ[R] (TensorProduct R C A)))) = (pullback.snd ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))) ≫ (pullback.snd f (Spec.map (CommRingCat.ofHom φ))) := by
    simp only [E, Iso.trans_hom, Category.assoc, pullbackSpecIso_hom_snd, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id, pullbackRightPullbackFstIso_hom_snd]
  let Λ : (TensorProduct R C A) →+* ((pullback ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).presheaf.obj (op ⊤)) :=
    E.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of (TensorProduct R C A))).inv.hom
  have hΛsurj : Function.Surjective Λ := by
    intro y
    refine ⟨(Scheme.ΓSpecIso (.of (TensorProduct R C A))).hom.hom (E.inv.appTop.hom y), ?_⟩
    change E.hom.appTop.hom ((Scheme.ΓSpecIso _).inv.hom ((Scheme.ΓSpecIso _).hom.hom (E.inv.appTop.hom y))) = y
    rw [← CommRingCat.comp_apply (Scheme.ΓSpecIso _).hom, Iso.hom_inv_id, CommRingCat.id_apply,
      ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, E.hom_inv_id]
    simp
  have hΛC : ∀ b : C, Λ (TensorProduct.tmul R b 1) = (pullback.fst ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).appTop.hom ((Scheme.ΓSpecIso (.of C)).inv b) := by
    intro b
    have h1 := CommRingCat.hom_ext_iff.mp (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : C →+* (TensorProduct R C A))))
    have h2 := RingHom.congr_fun h1 b
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
    change E.hom.appTop.hom ((Scheme.ΓSpecIso _).inv.hom (Algebra.TensorProduct.includeLeftRingHom b)) = _
    erw [h2]
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hE1]
  have hΛA : ∀ a : A, Λ (TensorProduct.tmul R 1 a) = ((pullback.snd ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))) ≫ (pullback.snd f (Spec.map (CommRingCat.ofHom φ)))).appTop.hom ((Scheme.ΓSpecIso (.of A)).inv a) := by
    intro a
    have h1 := CommRingCat.hom_ext_iff.mp (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight : A →ₐ[R] (TensorProduct R C A)))))
    have h2 := RingHom.congr_fun h1 a
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
    change E.hom.appTop.hom ((Scheme.ΓSpecIso _).inv.hom ((RingHomClass.toRingHom (Algebra.TensorProduct.includeRight : A →ₐ[R] (TensorProduct R C A))) a)) = _
    erw [h2]
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hE2]
  have hgenP : ∀ y : ((pullback ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).presheaf.obj (op ⊤)), y ∈ Subring.closure (Set.range (fun b : C => (pullback.fst ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).appTop.hom ((Scheme.ΓSpecIso (.of C)).inv b)) ∪
       Set.range (fun a : A => ((pullback.snd ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))) ≫ (pullback.snd f (Spec.map (CommRingCat.ofHom φ)))).appTop.hom ((Scheme.ΓSpecIso (.of A)).inv a))) := by
    intro y
    obtain ⟨t, rfl⟩ := hΛsurj y
    refine TensorProduct.inductionOn t ?_ ?_
    ·
      intro b a
      rw [show TensorProduct.tmul R b a = (TensorProduct.tmul R b (1 : A)) * (TensorProduct.tmul R (1 : C) a) by rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul], map_mul, hΛC, hΛA]
      exact mul_mem (Subring.subset_closure (Or.inl ⟨b, rfl⟩)) (Subring.subset_closure (Or.inr ⟨a, rfl⟩))
    ·
      intro x y hx hy
      rw [map_add]
      apply add_mem hx hy
  have hVg : ((Scheme.Hom.opensFunctor (pullback.snd ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ))))).obj ⊤) = (((TopologicalSpace.Opens.map (pullback.fst f (Spec.map (CommRingCat.ofHom φ))).base).obj ((Scheme.Hom.opensFunctor ι).obj ⊤))) := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_pullbackSnd, Scheme.Hom.image_top_eq_opensRange]
  have hle : (⊤ : (pullback ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).Opens) ≤ ((TopologicalSpace.Opens.map (pullback.snd ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).base).obj (((TopologicalSpace.Opens.map (pullback.fst f (Spec.map (CommRingCat.ofHom φ))).base).obj ((Scheme.Hom.opensFunctor ι).obj ⊤)))) := by
    rw [← hVg, Scheme.Hom.preimage_image_eq]
  have hΨinj : Function.Injective ((pullback.snd ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).appLE (((TopologicalSpace.Opens.map (pullback.fst f (Spec.map (CommRingCat.ofHom φ))).base).obj ((Scheme.Hom.opensFunctor ι).obj ⊤))) ⊤ hle).hom := by
    have hΨ' : (pullback.snd ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).appLE (((TopologicalSpace.Opens.map (pullback.fst f (Spec.map (CommRingCat.ofHom φ))).base).obj ((Scheme.Hom.opensFunctor ι).obj ⊤))) ⊤ hle = (pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf.map (eqToHom hVg).op ≫ ((pullback.snd ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).appIso ⊤).hom := by
      rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE']
    rw [hΨ']
    apply (((pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf.mapIso (eqToIso hVg).op).trans ((pullback.snd ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).appIso ⊤)).commRingCatIsoToRingEquiv.injective
  have hΨC : ∀ b : C, ((pullback.snd ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).appLE (((TopologicalSpace.Opens.map (pullback.fst f (Spec.map (CommRingCat.ofHom φ))).base).obj ((Scheme.Hom.opensFunctor ι).obj ⊤))) ⊤ hle).hom (((pullback.fst f (Spec.map (CommRingCat.ofHom φ))).app ((Scheme.Hom.opensFunctor ι).obj ⊤)).hom ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of C)).inv b))) =
      (pullback.fst ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).appTop.hom ((Scheme.ΓSpecIso (.of C)).inv b) := by
    intro b
    have e1 : (⊤ : (pullback ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).Opens) ≤ ((TopologicalSpace.Opens.map ((pullback.snd ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))) ≫ (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).base).obj ((Scheme.Hom.opensFunctor ι).obj ⊤)) := hle
    rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ hle]
    have e2 : (⊤ : (pullback ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).Opens) ≤ ((TopologicalSpace.Opens.map ((pullback.fst ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))) ≫ ι).base).obj ((Scheme.Hom.opensFunctor ι).obj ⊤)) := by
      rw [hcond]
      apply e1
    have step2 : ∀ (m m' : (pullback ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))) ⟶ X) (hm : m = m') (e : (⊤ : (pullback ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).Opens) ≤ ((TopologicalSpace.Opens.map m.base).obj ((Scheme.Hom.opensFunctor ι).obj ⊤))) (e' : (⊤ : (pullback ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).Opens) ≤ ((TopologicalSpace.Opens.map m'.base).obj ((Scheme.Hom.opensFunctor ι).obj ⊤))), m.appLE ((Scheme.Hom.opensFunctor ι).obj ⊤) ⊤ e =
        m'.appLE ((Scheme.Hom.opensFunctor ι).obj ⊤) ⊤ e' := by
      intro m m' hm e e'
      subst hm
      rfl
    rw [step2 _ _ hcond.symm _ e2, ← Scheme.Hom.appLE_comp_appLE (pullback.fst ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))) ι ((Scheme.Hom.opensFunctor ι).obj ⊤) ⊤ ⊤ (by rw [Scheme.Hom.preimage_image_eq]) le_top,
      CommRingCat.comp_apply, ← CommRingCat.comp_apply (ι.appIso ⊤).inv, Scheme.Hom.appIso_inv_appLE]
    simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, CommRingCat.id_apply, appLE_top]
  have hΨA : ∀ a : A, ((pullback.snd ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).appLE (((TopologicalSpace.Opens.map (pullback.fst f (Spec.map (CommRingCat.ofHom φ))).base).obj ((Scheme.Hom.opensFunctor ι).obj ⊤))) ⊤ hle).hom (((pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf.map (homOfLE (le_top : (((TopologicalSpace.Opens.map (pullback.fst f (Spec.map (CommRingCat.ofHom φ))).base).obj ((Scheme.Hom.opensFunctor ι).obj ⊤))) ≤ ⊤)).op).hom ((pullback.snd f (Spec.map (CommRingCat.ofHom φ))).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))) =
      ((pullback.snd ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))) ≫ (pullback.snd f (Spec.map (CommRingCat.ofHom φ)))).appTop.hom ((Scheme.ΓSpecIso (.of A)).inv a) := by
    intro a
    rw [← CommRingCat.comp_apply ((pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf.map _), Scheme.Hom.map_appLE]
    change ((pullback.snd f (Spec.map (CommRingCat.ofHom φ))).appTop ≫ (pullback.snd ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).appLE ⊤ ⊤ _).hom _ = _
    rw [← appLE_top (pullback.snd f (Spec.map (CommRingCat.ofHom φ))) le_top, Scheme.Hom.appLE_comp_appLE, appLE_top]
  rw [eq_top_iff]
  rintro x -
  have hx := hgenP (((pullback.snd ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).appLE (((TopologicalSpace.Opens.map (pullback.fst f (Spec.map (CommRingCat.ofHom φ))).base).obj ((Scheme.Hom.opensFunctor ι).obj ⊤))) ⊤ hle).hom x)
  have hsub : Subring.closure (Set.range (fun b : C => (pullback.fst ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).appTop.hom ((Scheme.ΓSpecIso (.of C)).inv b)) ∪
       Set.range (fun a : A => ((pullback.snd ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))) ≫ (pullback.snd f (Spec.map (CommRingCat.ofHom φ)))).appTop.hom ((Scheme.ΓSpecIso (.of A)).inv a))) ≤
      (Subring.closure  (Set.range (fun b : C => ((pullback.fst f (Spec.map (CommRingCat.ofHom φ))).app ((Scheme.Hom.opensFunctor ι).obj ⊤)).hom
              ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of C)).inv b))) ∪
           Set.range (fun a : A => ((pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf.map
              (homOfLE (le_top : ((TopologicalSpace.Opens.map (pullback.fst f (Spec.map (CommRingCat.ofHom φ))).base).obj ((Scheme.Hom.opensFunctor ι).obj ⊤)) ≤ ⊤)).op).hom
              ((pullback.snd f (Spec.map (CommRingCat.ofHom φ))).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))))).map ((pullback.snd ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).appLE (((TopologicalSpace.Opens.map (pullback.fst f (Spec.map (CommRingCat.ofHom φ))).base).obj ((Scheme.Hom.opensFunctor ι).obj ⊤))) ⊤ hle).hom := by
    rw [Subring.closure_le]
    rintro y (⟨b, rfl⟩ | ⟨a, rfl⟩)
    · exact ⟨_, Subring.subset_closure (Or.inl ⟨b, rfl⟩), hΨC b⟩
    · exact ⟨_, Subring.subset_closure (Or.inr ⟨a, rfl⟩), hΨA a⟩
  obtain ⟨x', hx', hxx'⟩ := hsub hx
  exact hΨinj hxx' ▸ hx'
set_option maxHeartbeats 999999 in
/--
[AlgebraicGeometry_exists_opens_restrict_mul_eq_restrict_of_mem_closure_chart_sections](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_opens_restrict_mul_eq_restrict_of_mem_closure_chart_sections.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] {X : (Scheme : Type (u + 1))} (f : X ⟶ Spec (CommRingCat.of R))
  (C : Type u) [CommRing C] [Algebra R C] (ι : Spec (CommRingCat.of C) ⟶ X) [IsOpenImmersion ι]
  (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R C)))
  {A : Type u} [CommRing A] (φ : R →+* A)
  (z : ↥(pullback f (Spec.map (CommRingCat.ofHom φ))))
  (hz : (pullback.fst f (Spec.map (CommRingCat.ofHom φ))).base z ∈ (Scheme.Hom.opensFunctor ι).obj ⊤)
  (U : (pullback f (Spec.map (CommRingCat.ofHom φ))).Opens) (hzU : z ∈ U)
  (s : ((pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf.obj (op U))) :
  ∃ (W : (pullback f (Spec.map (CommRingCat.ofHom φ))).Opens) (_ : z ∈ W) (hWU : W ≤ U) (hWV : W ≤ ((TopologicalSpace.Opens.map (pullback.fst f (Spec.map (CommRingCat.ofHom φ))).base).obj ((Scheme.Hom.opensFunctor ι).obj ⊤))) (σ τ : ((pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf.obj (op ((TopologicalSpace.Opens.map (pullback.fst f (Spec.map (CommRingCat.ofHom φ))).base).obj ((Scheme.Hom.opensFunctor ι).obj ⊤))))), σ ∈ Subring.closure
    (Set.range (fun b : C => ((pullback.fst f (Spec.map (CommRingCat.ofHom φ))).app ((Scheme.Hom.opensFunctor ι).obj ⊤)).hom
        ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of C)).inv b))) ∪
     Set.range (fun a : A => ((pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf.map
        (homOfLE (le_top : ((TopologicalSpace.Opens.map (pullback.fst f (Spec.map (CommRingCat.ofHom φ))).base).obj ((Scheme.Hom.opensFunctor ι).obj ⊤)) ≤ ⊤)).op).hom
        ((pullback.snd f (Spec.map (CommRingCat.ofHom φ))).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)))) ∧
    τ ∈ Subring.closure
    (Set.range (fun b : C => ((pullback.fst f (Spec.map (CommRingCat.ofHom φ))).app ((Scheme.Hom.opensFunctor ι).obj ⊤)).hom
        ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of C)).inv b))) ∪
     Set.range (fun a : A => ((pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf.map
        (homOfLE (le_top : ((TopologicalSpace.Opens.map (pullback.fst f (Spec.map (CommRingCat.ofHom φ))).base).obj ((Scheme.Hom.opensFunctor ι).obj ⊤)) ≤ ⊤)).op).hom
        ((pullback.snd f (Spec.map (CommRingCat.ofHom φ))).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)))) ∧
    IsUnit (((pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf.map (homOfLE hWV).op).hom τ) ∧
    ((pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf.map (homOfLE hWU).op).hom s *
        ((pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf.map (homOfLE hWV).op).hom τ =
      ((pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf.map (homOfLE hWV).op).hom σ := by
  classical
  have hV := isAffineOpen_V f C ι hι φ
  set V : (pullback f (Spec.map (CommRingCat.ofHom φ))).Opens := ((TopologicalSpace.Opens.map (pullback.fst f (Spec.map (CommRingCat.ofHom φ))).base).obj ((Scheme.Hom.opensFunctor ι).obj ⊤)) with hVdef
  have hzV : z ∈ V := hz
  obtain ⟨r, hrU, hzr⟩ := hV.exists_basicOpen_le ⟨z, hzU⟩ hzV
  have hWV : (pullback f (Spec.map (CommRingCat.ofHom φ))).basicOpen r ≤ V := (pullback f (Spec.map (CommRingCat.ofHom φ))).basicOpen_le r
  let _ := hV.isLocalization_basicOpen r
  obtain ⟨⟨σ, ⟨_, n, rfl⟩⟩, hst⟩ :=
    IsLocalization.surj (Submonoid.powers r) (((pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf.map (homOfLE hrU).op).hom s)
  have hgen := closure_eq_top f C ι hι φ
  refine ⟨(pullback f (Spec.map (CommRingCat.ofHom φ))).basicOpen r, hzr, hrU, hWV, σ, r ^ n, ?_, ?_, ?_, ?_⟩
  ·
    rw [hgen]
    apply Subring.mem_top
  ·
    rw [hgen]
    apply Subring.mem_top
  ·
    rw [map_pow]
    apply (IsLocalization.Away.algebraMap_isUnit (S := ((pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf.obj (op ((pullback f (Spec.map (CommRingCat.ofHom φ))).basicOpen r)))) r).pow n
  · apply hst


-- created on 2026-10-20
