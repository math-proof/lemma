import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

variable {A A₁ : Type u} [CommRing A] [IsLocalRing A] [CommRing A₁]
  (ι₁ : A₁ →+* A)
private lemma ringHom_ext_of_ι₁
  (hres₁ : Function.Surjective ((residue A).comp ι₁)) {T : Type*} [CommRing T] (φ ψ : A →+* T)
    (hφ : ∀ t ∈ maximalIdeal A, φ t = 0) (hψ : ∀ t ∈ maximalIdeal A, ψ t = 0)
    (h : ∀ a₁, φ (ι₁ a₁) = ψ (ι₁ a₁)) : φ = ψ := by
  ext a
  obtain ⟨a₁, ha₁⟩ := hres₁ (residue A a)
  have : a - ι₁ a₁ ∈ maximalIdeal A := by
    rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]
    apply ha₁.symm
  have e1 := hφ _ this
  have e2 := hψ _ this
  rw [map_sub, sub_eq_zero] at e1 e2
  rw [e1, e2, h]
variable [IsLocalRing A₁] [IsLocalHom ι₁]
private lemma residueFieldMap_bijective
  (hres₁ : Function.Surjective ((residue A).comp ι₁)) : Function.Bijective (ResidueField.map ι₁) := by
  refine ⟨(ResidueField.map ι₁).injective, fun v => ?_⟩
  obtain ⟨a₁, ha₁⟩ := hres₁ v
  refine ⟨residue A₁ a₁, ?_⟩
  rwa [ResidueField.map_residue]
private noncomputable def resEquiv (hres₁ : Function.Surjective ((residue A).comp ι₁)) :
  ResidueField A₁ ≃+* ResidueField A :=
  RingEquiv.ofBijective (ResidueField.map ι₁) (residueFieldMap_bijective ι₁ hres₁)
private lemma resEquiv_symm_residue (hres₁ : Function.Surjective ((residue A).comp ι₁)) (a₁ : A₁) :
  (resEquiv ι₁ hres₁).symm (residue A (ι₁ a₁)) = residue A₁ a₁ := by
  apply (resEquiv ι₁ hres₁).injective
  rw [RingEquiv.apply_symm_apply]
  exact (ResidueField.map_residue ι₁ a₁).symm
variable (hres₁ : Function.Surjective ((residue A).comp ι₁)) {R : Type u} [CommRing R] (b : A₁ →+* R)
private noncomputable def lift₁
  : ResidueField A₁ →+* R ⧸ Ideal.map b (maximalIdeal A₁) :=
  Ideal.Quotient.lift (maximalIdeal A₁) ((Ideal.Quotient.mk (Ideal.map b (maximalIdeal A₁))).comp b)
    (fun a ha => by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ ha)
private lemma lift₁_residue (a₁ : A₁) :
  lift₁ b (residue A₁ a₁) = Ideal.Quotient.mk (Ideal.map b (maximalIdeal A₁)) (b a₁) := rfl
private noncomputable def aR
  : A →+* R ⧸ Ideal.map b (maximalIdeal A₁) :=
  (lift₁ b).comp ((resEquiv ι₁ hres₁).symm.toRingHom.comp (residue A))
private lemma aR_apply
  (t : A) : aR ι₁ hres₁ b t = lift₁ b ((resEquiv ι₁ hres₁).symm (residue A t)) := rfl
private lemma aR_ι₁ (a₁ : A₁) :
  aR ι₁ hres₁ b (ι₁ a₁) = Ideal.Quotient.mk (Ideal.map b (maximalIdeal A₁)) (b a₁) := by
  rw [aR_apply, resEquiv_symm_residue, lift₁_residue]
private lemma aR_comp_ι₁
  : (aR ι₁ hres₁ b).comp ι₁ = (Ideal.Quotient.mk (Ideal.map b (maximalIdeal A₁))).comp b :=
  RingHom.ext fun a₁ => aR_ι₁ ι₁ hres₁ b a₁
private lemma aR_eq_zero_of_mem
  {t : A} (ht : t ∈ maximalIdeal A) : aR ι₁ hres₁ b t = 0 := by
  rw [aR_apply, Iff.mpr (residue_eq_zero_iff t) ht, map_zero, map_zero]
variable {Z : (Scheme : Type (u + 1))}
private lemma map_op_congr {A B : Z.Opens} (i j : B ⟶ A) (s : Z.presheaf.obj (op A)) :
  Z.presheaf.map i.op s = Z.presheaf.map j.op s := by
  rw [Subsingleton.elim i j]
private lemma app_map_top {Z' : (Scheme : Type (u + 1))} (q : Z' ⟶ Z) (W : Z.Opens) (x : Z.presheaf.obj (op ⊤)) :
  q.app W (Z.presheaf.map (homOfLE le_top).op x) =
      Z'.presheaf.map (homOfLE le_top).op (q.appTop x) := by
  have := congrArg (fun φ => φ.hom x) (q.naturality (homOfLE (le_top : W ≤ ⊤)).op)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at this
  rw [this]
  exact map_op_congr _ _ _
private lemma comp_app_apply {X Y : (Scheme : Type (u + 1))} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens) (x : Z.presheaf.obj (op U)) :
  (f ≫ g).app U x = f.app (((TopologicalSpace.Opens.map g.base).obj U)) (g.app U x) := rfl
private lemma map_id_apply'
  {A : Z.Opens} (i : A ⟶ A) (s : Z.presheaf.obj (op A)) : Z.presheaf.map i.op s = s := by
  rw [Subsingleton.elim i (𝟙 _), op_id, Z.presheaf.map_id]
  rfl
private lemma map_congr' {A B : Z.Opens} (i j : op A ⟶ op B) (s : Z.presheaf.obj (op A)) :
  Z.presheaf.map i s = Z.presheaf.map j s := by
  rw [← i.op_unop, ← j.op_unop, Subsingleton.elim i.unop j.unop]
private lemma map_map_eq {A B C : Z.Opens} (i : op A ⟶ op B) (j : op B ⟶ op C) (s : Z.presheaf.obj (op A)) :
  Z.presheaf.map j (Z.presheaf.map i s) = Z.presheaf.map (i ≫ j) s := by
  rw [Z.presheaf.map_comp]
  rfl
private lemma map_top_endo
  (i : op (⊤ : Z.Opens) ⟶ op ⊤) (s : Z.presheaf.obj (op ⊤)) : Z.presheaf.map i s = s := by
  rw [map_congr' i (𝟙 _), Z.presheaf.map_id]
  rfl
variable {A A₁ : Type u} [CommRing A] [IsLocalRing A] [CommRing A₁] [IsLocalRing A₁]
private noncomputable def baseAt
  {B : Type u} [CommRing B] {Y : (Scheme : Type (u + 1))} (f : Y ⟶ Spec (CommRingCat.of B))
  (y : Y) : B →+* Y.presheaf.stalk y :=
  (Y.presheaf.germ ⊤ y trivial).hom.comp (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
private lemma baseAt_apply
  {B : Type u} [CommRing B] {Y : (Scheme : Type (u + 1))} (f : Y ⟶ Spec (CommRingCat.of B)) (y : Y)
  (t : B) : baseAt f y t = Y.presheaf.germ ⊤ y trivial (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of B)).inv t)) :=
  rfl
private lemma baseAt_mem_maximalIdeal
  {B : Type u} [CommRing B] [IsLocalRing B] {Y : (Scheme : Type (u + 1))}
  (f : Y ⟶ Spec (CommRingCat.of B)) (y : Y) (hy : f.base y = closedPoint B) {t : B} (ht : t ∈ maximalIdeal B) :
    baseAt f y t ∈ maximalIdeal (Y.presheaf.stalk y) := by
  rw [mem_maximalIdeal, mem_nonunits_iff, baseAt_apply]
  intro hu
  have hmem : y ∈ Y.basicOpen (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of B)).inv t)) :=
    Iff.mpr (Y.mem_basicOpen_top _ y) hu
  rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine] at hmem
  have hmem' : f.base y ∈ PrimeSpectrum.basicOpen t := hmem
  rw [hy] at hmem'
  exact Iff.mp (PrimeSpectrum.mem_basicOpen (R := B) t (closedPoint B)) hmem' ht
private lemma stalkMap_baseAt
  (ι₁ : A₁ →+* A) {X₁ P : (Scheme : Type (u + 1))} (f₁ : X₁ ⟶ Spec (CommRingCat.of A₁))
  (π : P ⟶ X₁) (β : P ⟶ Spec (CommRingCat.of A))
    (hw : π ≫ f₁ = β ≫ Spec.map (CommRingCat.ofHom ι₁)) (p : P) (a₁ : A₁) :
    (π.stalkMap p).hom (baseAt f₁ (π.base p) a₁) = baseAt β p (ι₁ a₁) := by
  have h2 := congrArg (fun φ => φ.appTop ((Scheme.ΓSpecIso (CommRingCat.of A₁)).inv a₁)) hw
  have h3 := congrArg (fun φ => φ.hom a₁)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ι₁))
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom] at h2 h3
  rw [baseAt_apply, baseAt_apply]
  erw [Scheme.Hom.germ_stalkMap_apply, h2, ← h3]
  rfl
set_option maxHeartbeats 999999 in
private lemma core
  (ι₁ : A₁ →+* A) [IsLocalHom ι₁] (hres₁ : Function.Surjective ((residue A).comp ι₁))
  {X₁ P : (Scheme : Type (u + 1))} (f₁ : X₁ ⟶ Spec (CommRingCat.of A₁))
    (π : P ⟶ X₁) (β : P ⟶ Spec (CommRingCat.of A))
    (hP : IsPullback π β f₁ (Spec.map (CommRingCat.ofHom ι₁)))
    (p : P) (hp : β.base p = closedPoint A)
    (r : X₁.presheaf.stalk (π.base p))
    (hr : (π.stalkMap p).hom r ∈ Ideal.map (baseAt β p) (maximalIdeal A)) :
    r ∈ Ideal.map (baseAt f₁ (π.base p)) (maximalIdeal A₁) := by
  set I : Ideal (X₁.presheaf.stalk (π.base p)) := Ideal.map (baseAt f₁ (π.base p)) (maximalIdeal A₁) with hI
  have hbase : ∀ a₁ : A₁, (π.stalkMap p).hom (baseAt f₁ (π.base p) a₁) = baseAt β p (ι₁ a₁) :=
    stalkMap_baseAt ι₁ f₁ π β hP.w p
  have hβmem : ∀ {t : A}, t ∈ maximalIdeal A → baseAt β p t ∈ maximalIdeal (P.presheaf.stalk p) :=
    fun ht => baseAt_mem_maximalIdeal β p hp ht
  have hIle : I ≤ maximalIdeal (X₁.presheaf.stalk (π.base p)) := by
    rw [hI, Ideal.map_le_iff_le_comap]
    intro a₁ ha₁
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff, ← isUnit_map_iff (π.stalkMap p).hom, hbase]
    exact Iff.mp (mem_maximalIdeal _) (hβmem (map_nonunit ι₁ a₁ ha₁))
  have hItop : I ≠ ⊤ := fun h => (maximalIdeal.isMaximal _).ne_top (Iff.mp top_le_iff (h ▸ hIle))
  let _ : Nontrivial (X₁.presheaf.stalk (π.base p) ⧸ I) := Iff.mpr Ideal.Quotient.nontrivial_iff hItop
  let _ : IsLocalRing (X₁.presheaf.stalk (π.base p) ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let q : X₁.presheaf.stalk (π.base p) ⟶ CommRingCat.of (X₁.presheaf.stalk (π.base p) ⧸ I) := CommRingCat.ofHom (Ideal.Quotient.mk I)
  have hq : ∀ z, q z = Ideal.Quotient.mk I z := fun z => rfl
  let hqloc : IsLocalHom q.hom := by
    refine ⟨fun x hx => ?_⟩
    by_contra hxu
    obtain ⟨wbar, hw⟩ := hx.exists_right_inv
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective wbar
    have h0 : Ideal.Quotient.mk I (x * w - 1) = 0 := by
      rw [map_sub, map_one, map_mul, sub_eq_zero]
      apply hw
    rw [Ideal.Quotient.eq_zero_iff_mem] at h0
    have h1 : x * w - 1 ∈ maximalIdeal _ := hIle h0
    have h2 : x * w ∈ maximalIdeal _ := Ideal.mul_mem_right _ _ (Iff.mpr (mem_maximalIdeal _) hxu)
    have h3 := (maximalIdeal (X₁.presheaf.stalk (π.base p))).sub_mem h2 h1
    rw [sub_sub_cancel] at h3
    exact (maximalIdeal.isMaximal _).ne_top (Iff.mpr (Ideal.eq_top_iff_one _) h3)
  let a : A →+* X₁.presheaf.stalk (π.base p) ⧸ I := aR ι₁ hres₁ (baseAt f₁ (π.base p))
  have ha₁ : ∀ a₁, a (ι₁ a₁) = Ideal.Quotient.mk I (baseAt f₁ (π.base p) a₁) := aR_ι₁ ι₁ hres₁ (baseAt f₁ (π.base p))
  have ha0 : ∀ t ∈ maximalIdeal A, a t = 0 := fun t ht => aR_eq_zero_of_mem ι₁ hres₁ (baseAt f₁ (π.base p)) ht
  have hw : (Spec.map q ≫ X₁.fromSpecStalk (π.base p)) ≫ f₁ =
      Spec.map (CommRingCat.ofHom a) ≫ Spec.map (CommRingCat.ofHom ι₁) := by
    apply ext_to_Spec
    ext t
    change ((Spec.map q ≫ X₁.fromSpecStalk (π.base p)) ≫ f₁).appTop ((Scheme.ΓSpecIso (CommRingCat.of A₁)).inv t) =
      (Spec.map (CommRingCat.ofHom a) ≫ Spec.map (CommRingCat.ofHom ι₁)).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of A₁)).inv t)
    have n1 := congrArg (fun φ => φ.hom (baseAt f₁ (π.base p) t)) (Scheme.ΓSpecIso_inv_naturality q)
    have n2 := congrArg (fun φ => φ.hom t) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ι₁))
    have n3 := congrArg (fun φ => φ.hom (ι₁ t)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom a))
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at n1 n2 n3
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
    rw [← n2, ← n3, ha₁, Scheme.fromSpecStalk_appTop]
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
    erw [app_map_top]
    rw [← baseAt_apply]
    erw [← n1]
    rw [hq]
  let σ := hP.lift (Spec.map q ≫ X₁.fromSpecStalk (π.base p)) (Spec.map (CommRingCat.ofHom a)) hw
  have hσ₁ : σ ≫ π = Spec.map q ≫ X₁.fromSpecStalk (π.base p) := hP.lift_fst _ _ _
  have hσ₂ : σ ≫ β = Spec.map (CommRingCat.ofHom a) := hP.lift_snd _ _ _
  have hts : ∀ t : A, (β.stalkMap p).hom (StructureSheaf.toStalk A (β.base p) t) = baseAt β p t := by
    intro t
    rw [baseAt_apply]
    erw [Scheme.Hom.germ_stalkMap_apply β ⊤ p trivial]
    rfl
  let χ : X₁.presheaf.stalk (π.base p) →+* P.residueField p := (P.residue p).hom.comp (π.stalkMap p).hom
  have hχ0 : ∀ z ∈ maximalIdeal (X₁.presheaf.stalk (π.base p)), χ z = 0 := by
    intro z hz
    change IsLocalRing.residue _ ((π.stalkMap p).hom z) = 0
    exact Iff.mpr (residue_eq_zero_iff _) (map_nonunit _ z hz)
  let ρ : X₁.presheaf.stalk (π.base p) ⧸ I →+* P.residueField p :=
    Ideal.Quotient.lift I χ (fun z hz => hχ0 z (hIle hz))
  have hρq : ∀ z, ρ (Ideal.Quotient.mk I z) = χ z := fun z => rfl
  let hρloc : IsLocalHom ρ := by
    refine ⟨fun x hx => ?_⟩
    by_contra hxu
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hz : ¬ IsUnit z := fun h => hxu (h.map _)
    rw [hρq, hχ0 z (Iff.mpr (mem_maximalIdeal _) hz)] at hx
    exact not_isUnit_zero hx
  let _ : IsLocalHom (CommRingCat.ofHom ρ).hom := hρloc
  let γ : Spec (P.residueField p) ⟶ Spec (CommRingCat.of (X₁.presheaf.stalk (π.base p) ⧸ I)) :=
    Spec.map (CommRingCat.ofHom ρ)
  have hγσ : γ ≫ σ = P.fromSpecResidueField p := by
    apply hP.hom_ext
    ·
      rw [Category.assoc, hσ₁, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
        Scheme.fromSpecResidueField, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
        Scheme.residue_residueFieldMap]
      rfl
    ·
      rw [Category.assoc, hσ₂, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
        Scheme.fromSpecResidueField, Spec.fromSpecStalk_eq', ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
      erw [← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      have eres := congrArg (fun φ => φ.hom) (Scheme.residue_residueFieldMap β p)
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at eres ⊢
      apply ringHom_ext_of_ι₁ ι₁ hres₁
      ·
        intro t ht
        simp only [RingHom.comp_apply]
        show ρ (a t) = 0
        rw [ha0 t ht, map_zero]
      ·
        intro t ht
        simp only [RingHom.comp_apply]
        have e1 := congrArg (fun φ => φ ((StructureSheaf.toStalk A (β.base p)).hom t)) eres
        simp only [RingHom.comp_apply] at e1
        erw [e1, hts]
        change IsLocalRing.residue _ (baseAt β p t) = 0
        exact Iff.mpr (residue_eq_zero_iff _) (hβmem ht)
      ·
        intro a₁
        simp only [RingHom.comp_apply]
        have e1 := congrArg (fun φ => φ ((StructureSheaf.toStalk A (β.base p)).hom (ι₁ a₁))) eres
        simp only [RingHom.comp_apply] at e1
        erw [e1, hts, ha₁, hρq, ← hbase]
        rfl
  have hσp : σ.base (closedPoint (X₁.presheaf.stalk (π.base p) ⧸ I)) = p := by
    have h1 : γ.base (closedPoint (P.residueField p)) = closedPoint (X₁.presheaf.stalk (π.base p) ⧸ I) :=
      Spec_closedPoint (f := CommRingCat.ofHom ρ)
    rw [← h1]
    change (γ ≫ σ).base (closedPoint _) = p
    rw [hγσ]
    exact Scheme.fromSpecResidueField_apply p _
  let e := P.presheaf.stalkCongr (Inseparable.of_eq hσp)
  let τ : P.presheaf.stalk p ⟶ CommRingCat.of (X₁.presheaf.stalk (π.base p) ⧸ I) := e.inv ≫ Scheme.stalkClosedPointTo σ
  have hτgerm : ∀ (W : P.Opens) (hW : p ∈ W) (s : P.presheaf.obj (op W)),
      ∃ hW' : σ.base (closedPoint (X₁.presheaf.stalk (π.base p) ⧸ I)) ∈ W,
        τ (P.presheaf.germ W p hW s) =
          (Scheme.ΓSpecIso (CommRingCat.of (X₁.presheaf.stalk (π.base p) ⧸ I))).hom
            ((Spec (CommRingCat.of (X₁.presheaf.stalk (π.base p) ⧸ I))).presheaf.map
              (eqToHom (Scheme.preimage_eq_top_of_closedPoint_mem σ (hσp.symm ▸ hW)).symm).op (σ.app W s)) := by
    intro W hW s
    refine ⟨hσp.symm ▸ hW, ?_⟩
    have hg : e.inv (P.presheaf.germ W p hW s) = P.presheaf.germ W _ (hσp.symm ▸ hW) s := by
      have := congrArg (fun φ => φ.hom s)
        (P.presheaf.germ_stalkSpecializes hW (Inseparable.of_eq hσp).le)
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at this
      exact this
    show Scheme.stalkClosedPointTo σ (e.inv (P.presheaf.germ W p hW s)) = _
    rw [hg]
    have := congrArg (fun φ => φ.hom s) (Scheme.germ_stalkClosedPointTo σ W (hσp.symm ▸ hW))
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, Iso.trans_hom,
      Functor.mapIso_hom, Iso.op_hom, eqToIso.hom] at this
    exact this
  have hih : ∀ w, (Scheme.ΓSpecIso (CommRingCat.of (X₁.presheaf.stalk (π.base p) ⧸ I))).hom
    ((Scheme.ΓSpecIso (CommRingCat.of (X₁.presheaf.stalk (π.base p) ⧸ I))).inv w) = w := fun w => by
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id]
    rfl
  have hD1 : ∀ z : X₁.presheaf.stalk (π.base p), τ ((π.stalkMap p).hom z) = Ideal.Quotient.mk I z := by
    intro z
    obtain ⟨U, hU, s, rfl⟩ := X₁.presheaf.exists_germ_eq z
    erw [Scheme.Hom.germ_stalkMap_apply π U p hU]
    obtain ⟨hW', e1⟩ := hτgerm (((TopologicalSpace.Opens.map π.base).obj U)) hU (π.app U s)
    rw [e1, ← comp_app_apply]
    have e2 := congrArg (fun φ => φ.hom s) (Scheme.Hom.congr_app hσ₁ U)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at e2
    rw [e2, comp_app_apply, Scheme.fromSpecStalk_app hU]
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
    erw [app_map_top]
    have n1 := congrArg (fun φ => φ.hom (X₁.presheaf.germ U (π.base p) hU s)) (Scheme.ΓSpecIso_inv_naturality q)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at n1
    erw [← n1]
    try
      rw [map_map_eq, map_map_eq, map_top_endo]
      erw [hih, hq]
    catch _ =>
      try
        erw [hih, hq]
      catch _ =>
        rw [map_map_eq, map_top_endo]
        erw [hih, hq]
  have hD2 : ∀ t : A, τ (baseAt β p t) = a t := by
    intro t
    change τ (P.presheaf.germ (((TopologicalSpace.Opens.map β.base).obj ⊤)) p trivial (β.app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv t))) = a t
    obtain ⟨hW', e1⟩ := hτgerm (((TopologicalSpace.Opens.map β.base).obj ⊤)) trivial (β.app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv t))
    rw [e1, ← comp_app_apply]
    have e2 := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv t)) (Scheme.Hom.congr_app hσ₂ ⊤)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at e2
    rw [e2]
    have n3 := congrArg (fun φ => φ.hom t) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom a))
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at n3
    erw [← n3]
    try
      rw [map_map_eq, map_top_endo]
      apply hih _
    catch _ =>
      try
        apply hih _
      catch _ =>
        rw [map_map_eq, map_map_eq, map_top_endo]
        apply hih _
  have hmem : τ.hom ((π.stalkMap p).hom r) ∈ Ideal.map (τ.hom.comp (baseAt β p)) (maximalIdeal A) := by
    rw [← Ideal.map_map]
    apply Ideal.mem_map_of_mem _ hr
  have hcomp : τ.hom.comp (baseAt β p) = a := RingHom.ext hD2
  have hbot : Ideal.map a (maximalIdeal A) = ⊥ := by
    rw [Ideal.map_eq_bot_iff_le_ker]
    intro t ht
    apply ha0 t ht
  rw [hcomp, hbot, Ideal.mem_bot] at hmem
  have : Ideal.Quotient.mk I r = 0 := (hD1 r).symm.trans hmem
  exact Iff.mp Ideal.Quotient.eq_zero_iff_mem this
/--
[AlgebraicGeometry_mem_map_maximalIdeal_of_stalkMap_mem_map_maximalIdeal_of_iso_pullback](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_mem_map_maximalIdeal_of_stalkMap_mem_map_maximalIdeal_of_iso_pullback.lean)
-/
@[path]
private lemma main
  {A A₁ : Type u} [CommRing A] [IsLocalRing A] [CommRing A₁] [IsLocalRing A₁]
    (ι₁ : A₁ →+* A) [IsLocalHom ι₁] (hres₁ : Function.Surjective ((IsLocalRing.residue A).comp ι₁))
    {X X₁ : (Scheme : Type (u + 1))} (toBase : X ⟶ Spec (CommRingCat.of A)) (f₁ : X₁ ⟶ Spec (CommRingCat.of A₁))
    (e₁ : X ≅ pullback f₁ (Spec.map (CommRingCat.ofHom ι₁)))
    (he₁ : e₁.hom ≫ pullback.snd f₁ (Spec.map (CommRingCat.ofHom ι₁)) = toBase)
    (x : X) (hx : toBase.base x = IsLocalRing.closedPoint A)
    (r : X₁.presheaf.stalk ((e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x))
    (hr : ((e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).stalkMap x).hom r ∈
      Ideal.map ((X.presheaf.germ ⊤ x trivial).hom.comp
        (toBase.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
        (IsLocalRing.maximalIdeal A)) :
    r ∈ Ideal.map ((X₁.presheaf.germ ⊤ ((e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base x)
        trivial).hom.comp (f₁.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A₁)).inv.hom))
      (IsLocalRing.maximalIdeal A₁) := by
  apply core ι₁ hres₁ f₁ _ toBase
    (IsPullback.of_iso_pullback ⟨by rw [Category.assoc, pullback.condition, ← Category.assoc, he₁]⟩ e₁ rfl he₁)
    x hx r hr


-- created on 2026-10-20
