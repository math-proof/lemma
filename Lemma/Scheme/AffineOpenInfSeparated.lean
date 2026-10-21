import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma opHom_eq
  {X : (Scheme : Type (u + 1))}
  {A B : X.Opens}
  (i j : op A ⟶ op B) :
  -- imply
  i = j :=
  Quiver.Hom.unop_inj (Subsingleton.elim _ _)

private lemma topIso_hom_homOfLE_appTop
  {X : (Scheme : Type (u + 1))}
  {U W : X.Opens}
  (e : W ≤ U)
  (a : X.presheaf.obj (op U)) :
  -- imply
  W.topIso.hom ((X.homOfLE e).appTop (U.topIso.inv a)) = X.presheaf.map (homOfLE e).op a := by
  -- proof
  rw [Scheme.homOfLE_appTop]
  simp only [Scheme.Opens.topIso_hom, Scheme.Opens.topIso_inv]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
  change (X.presheaf.map _ ≫ X.presheaf.map _ ≫ X.presheaf.map _) a = _
  rw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
  apply congrArg (fun i => X.presheaf.map i a) (opHom_eq _ _)

private lemma exists_eq_specMap
  {A R : (CommRingCat : Type (u + 1))}
  (g : Spec A ⟶ Spec R) :
  -- imply
  ∃ θ : R ⟶ A, Spec.map θ = g := by
  -- proof
  refine ⟨(Scheme.ΓSpecIso R).inv ≫ g.appTop ≫ (Scheme.ΓSpecIso A).hom, ?_⟩
  have h := Scheme.toSpecΓ_naturality g
  rw [← SpecMap_ΓSpecIso_hom, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp] at h
  rw [Spec.map_comp, ← h, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]

/--
[AlgebraicGeometry_IsSeparated_isAffineOpen_inf_and_exists_eq_sum_mul_of_isAffineOpen](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_IsSeparated_isAffineOpen_inf_and_exists_eq_sum_mul_of_isAffineOpen.lean)
-/
@[path]
private lemma main
  {X Y : (Scheme : Type (u + 1))}
  (f : X ⟶ Y) [IsSeparated f] [IsAffine Y]
  (U V : X.Opens)
  -- given
  (hU : IsAffineOpen U)
  (hV : IsAffineOpen V) :
  -- imply
  IsAffineOpen (U ⊓ V) ∧ ∀ c : X.presheaf.obj (op (U ⊓ V)), ∃ (n : ℕ) (a : Fin n → X.presheaf.obj (op U)) (b : Fin n → X.presheaf.obj (op V)), c = ∑ i : Fin n, X.presheaf.map (homOfLE inf_le_left).op (a i) * X.presheaf.map (homOfLE inf_le_right).op (b i) := by
  -- proof
  classical
  set R : (CommRingCat : Type (u + 1)) := Y.presheaf.obj (op ⊤)
  set A : (CommRingCat : Type (u + 1)) := X.presheaf.obj (op U)
  set B : (CommRingCat : Type (u + 1)) := X.presheaf.obj (op V)
  set f' : X ⟶ Spec R := f ≫ Y.isoSpec.hom
  let _ : IsSeparated f' := inferInstance
  obtain ⟨θU, hθU⟩ := exists_eq_specMap (hU.fromSpec ≫ f')
  obtain ⟨θV, hθV⟩ := exists_eq_specMap (hV.fromSpec ≫ f')
  let _ : Algebra R A := θU.hom.toAlgebra
  let _ : Algebra R B := θV.hom.toAlgebra
  have eU : hU.fromSpec ≫ f' = Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
    rw [← hθU]
    rfl
  have eV : hV.fromSpec ≫ f' = Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
    rw [← hθV]
    rfl
  have hP : IsPullback (X.homOfLE (inf_le_left : U ⊓ V ≤ U) ≫ hU.isoSpec.hom) (X.homOfLE (inf_le_right : U ⊓ V ≤ V) ≫ hV.isoSpec.hom) hU.fromSpec hV.fromSpec :=
    (isPullback_opens_inf U V).of_iso (Iso.refl _) hU.isoSpec hV.isoSpec (Iso.refl _) (by simp) (by simp) (by simp [IsAffineOpen.isoSpec_hom]) (by simp [IsAffineOpen.isoSpec_hom])
  set ψ := pullback.mapDesc hU.fromSpec hV.fromSpec f' with hψ
  let _ : IsClosedImmersion ψ := inferInstance
  set F : (U ⊓ V).toScheme ⟶ Spec (CommRingCat.of (TensorProduct R A B)) :=
    hP.isoPullback.hom ≫ ψ ≫ (pullback.congrHom eU eV).hom ≫ (pullbackSpecIso R A B).hom with hF
  let hFci : IsClosedImmersion F := inferInstance
  obtain ⟨hAff, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine F
  refine ⟨hAff, ?_⟩
  have hF1 : F ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) = X.homOfLE inf_le_left ≫ hU.isoSpec.hom := by
    rw [hF, hψ]
    simp only [Category.assoc, pullbackSpecIso_hom_fst, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id, IsPullback.isoPullback_hom_fst]
  have hF2 : F ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B) : RingHom B (TensorProduct R A B))) = X.homOfLE inf_le_right ≫ hV.isoSpec.hom := by
    rw [hF, hψ]
    simp only [Category.assoc, pullbackSpecIso_hom_snd, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id, IsPullback.isoPullback_hom_snd]
  set Φ : RingHom (TensorProduct R A B) (X.presheaf.obj (op (U ⊓ V))) :=
    ((Scheme.ΓSpecIso (CommRingCat.of (TensorProduct R A B))).inv ≫ F.appTop ≫ (U ⊓ V).topIso.hom).hom with hΦ
  have hΦU : ∀ a : A, Φ (TensorProduct.tmul R a (1 : B)) = X.presheaf.map (homOfLE inf_le_left).op a := by
    intro a
    have h1 : (Scheme.ΓSpecIso (CommRingCat.of (TensorProduct R A B))).inv (TensorProduct.tmul R a (1 : B)) = (Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)).appTop ((Scheme.ΓSpecIso A).inv a) := by
      rw [← CommRingCat.comp_apply (Scheme.ΓSpecIso A).inv, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
      rfl
    have h2 : F.appTop ((Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)).appTop ((Scheme.ΓSpecIso A).inv a)) = (X.homOfLE inf_le_left).appTop (hU.isoSpec.hom.appTop ((Scheme.ΓSpecIso A).inv a)) := by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hF1, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      rfl
    have h3 : hU.isoSpec.hom.appTop ((Scheme.ΓSpecIso A).inv a) = U.topIso.inv a := by
      rw [IsAffineOpen.isoSpec_hom_appTop, CommRingCat.comp_apply, ← CommRingCat.comp_apply (Scheme.ΓSpecIso A).inv, Iso.inv_hom_id, CommRingCat.id_apply]
    simp only [hΦ, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
    rw [h1, h2, h3]
    apply topIso_hom_homOfLE_appTop _ a
  have hΦV : ∀ b : B, Φ (TensorProduct.tmul R (1 : A) b) = X.presheaf.map (homOfLE inf_le_right).op b := by
    intro b
    have h1 : (Scheme.ΓSpecIso (CommRingCat.of (TensorProduct R A B))).inv (TensorProduct.tmul R (1 : A) b) = (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B) : RingHom B (TensorProduct R A B)))).appTop ((Scheme.ΓSpecIso B).inv b) := by
      have nat := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B) : RingHom B (TensorProduct R A B)))
      have hnat := congrArg (fun φ => φ.hom b) nat
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hnat
      rw [← Algebra.TensorProduct.includeRight_apply (R := R) (A := A)]
      apply hnat
    have h2 : F.appTop ((Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B) : RingHom B (TensorProduct R A B)))).appTop ((Scheme.ΓSpecIso B).inv b)) = (X.homOfLE inf_le_right).appTop (hV.isoSpec.hom.appTop ((Scheme.ΓSpecIso B).inv b)) := by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hF2, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      rfl
    have h3 : hV.isoSpec.hom.appTop ((Scheme.ΓSpecIso B).inv b) = V.topIso.inv b := by
      rw [IsAffineOpen.isoSpec_hom_appTop, CommRingCat.comp_apply, ← CommRingCat.comp_apply (Scheme.ΓSpecIso B).inv, Iso.inv_hom_id, CommRingCat.id_apply]
    simp only [hΦ, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
    rw [h1, h2, h3]
    apply topIso_hom_homOfLE_appTop _ b
  intro c
  obtain ⟨s, hs⟩ := hsurj ((U ⊓ V).topIso.inv c)
  set t : TensorProduct R A B := (Scheme.ΓSpecIso (CommRingCat.of (TensorProduct R A B))).hom s with ht
  have hc : Φ t = c := by
    simp only [hΦ, ht, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
    rw [← CommRingCat.comp_apply (Scheme.ΓSpecIso _).hom, Iso.hom_inv_id, CommRingCat.id_apply, hs, ← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset t
  refine ⟨S.card, fun i => (S.equivFin.symm i).1.1, fun i => (S.equivFin.symm i).1.2, ?_⟩
  rw [← hc, hS, map_sum]
  rw [← Finset.sum_coe_sort S]
  rw [← Fintype.sum_equiv S.equivFin.symm (fun i => X.presheaf.map (homOfLE inf_le_left).op (S.equivFin.symm i).1.1 * X.presheaf.map (homOfLE inf_le_right).op (S.equivFin.symm i).1.2) (fun p => Φ (TensorProduct.tmul R p.1.1 p.1.2)) _]
  intro i
  dsimp
  rw [← hΦU, ← hΦV, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]


-- created on 2026-10-20
