import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma finrank_add_of_bijective_prod
  [CommRing R] [CommRing A] [CommRing A₁] [CommRing A₂]
  (φ : RingHom R A)
  (r₁ : RingHom A A₁)
  (r₂ : RingHom A A₂)
  -- given
  (hbij : Function.Bijective (RingHom.prod r₁ r₂))
  (h₁fin : (r₁.comp φ).Finite)
  (h₁flat : (r₁.comp φ).Flat)
  (h₂fin : (r₂.comp φ).Finite)
  (h₂flat : (r₂.comp φ).Flat)
  (x : PrimeSpectrum R) :
  -- imply
  (r₁.comp φ).finrank x + (r₂.comp φ).finrank x = φ.finrank x := by
  -- proof
  let _ : Algebra R A := φ.toAlgebra
  let _ : Algebra R A₁ := (r₁.comp φ).toAlgebra
  let _ : Algebra R A₂ := (r₂.comp φ).toAlgebra
  let _ : Module.Finite R A₁ := h₁fin
  let _ : Module.Flat R A₁ := h₁flat
  let _ : Module.Finite R A₂ := h₂fin
  let _ : Module.Flat R A₂ := h₂flat
  let e : LinearEquiv (RingHom.id R) A (A₁ × A₂) := {
    toFun := fun a => (r₁ a, r₂ a)
    map_add' := fun a b => by simp
    map_smul' := fun c a => by
      ext
      ·
        change r₁ (φ c * a) = (r₁.comp φ) c * r₁ a
        rw [map_mul]
        rfl
      ·
        change r₂ (φ c * a) = (r₂.comp φ) c * r₂ a
        rw [map_mul]
        rfl
    invFun := fun p => (Equiv.ofBijective _ hbij).symm p
    left_inv := fun a => (Equiv.ofBijective _ hbij).left_inv a
    right_inv := fun p => (Equiv.ofBijective _ hbij).right_inv p
  }
  change Module.rankAtStalk A₁ x + Module.rankAtStalk A₂ x = Module.rankAtStalk A x
  rw [Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_prod]
  rfl

private lemma bijective_restrict_prod
  {X : (Scheme : Type (u + 1))}
  (U V : X.Opens)
  -- given
  (hUV : U ⊔ V = ⊤)
  (hdisj : U ⊓ V = ⊥) :
  -- imply
  Function.Bijective (RingHom.prod (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom) := by
  -- proof
  have hnot : ∀ x : X, x ∉ U ⊓ V := by
    intro x hx
    rw [hdisj] at hx
    apply hx
  constructor
  ·
    intro a b hab
    have h1 : X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op a = X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op b :=
      congrArg Prod.fst hab
    have h2 : X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op a = X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op b :=
      congrArg Prod.snd hab
    apply TopCat.Presheaf.section_ext X.sheaf ⊤ a b
    intro x hx
    have hx' : x ∈ U ⊔ V := by
      rw [hUV]
      trivial
    obtain hU | hV := hx'
    ·
      have ha := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (le_top : U ≤ ⊤)) x hU a
      have hb := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (le_top : U ≤ ⊤)) x hU b
      change X.presheaf.germ ⊤ x _ a = X.presheaf.germ ⊤ x _ b
      rw [← ha, ← hb, h1]
    ·
      have ha := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (le_top : V ≤ ⊤)) x hV a
      have hb := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (le_top : V ≤ ⊤)) x hV b
      change X.presheaf.germ ⊤ x _ a = X.presheaf.germ ⊤ x _ b
      rw [← ha, ← hb, h2]
  ·
    rintro ⟨b, c⟩
    let p : RingHom.eqLocus (RingHom.comp (X.sheaf.obj.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op).hom (RingHom.fst (X.sheaf.obj.obj (op U)) (X.sheaf.obj.obj (op V)))) (RingHom.comp (X.sheaf.obj.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op).hom (RingHom.snd (X.sheaf.obj.obj (op U)) (X.sheaf.obj.obj (op V)))) :=
      ⟨(b, c), TopCat.Presheaf.section_ext X.sheaf (U ⊓ V) _ _ (fun x hx => absurd hx (hnot x))⟩
    let s : X.presheaf.obj (op (U ⊔ V)) := (X.sheaf.objSupIsoProdEqLocus U V).inv p
    have hsU : X.presheaf.map (homOfLE (le_sup_left : U ≤ U ⊔ V)).op s = b :=
      TopCat.Sheaf.objSupIsoProdEqLocus_inv_fst X.sheaf U V p
    have hsV : X.presheaf.map (homOfLE (le_sup_right : V ≤ U ⊔ V)).op s = c :=
      TopCat.Sheaf.objSupIsoProdEqLocus_inv_snd X.sheaf U V p
    have htop : (⊤ : X.Opens) ≤ U ⊔ V := hUV.symm.le
    refine ⟨X.presheaf.map (homOfLE htop).op s, ?_⟩
    ext
    ·
      change X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (X.presheaf.map (homOfLE htop).op s) = b
      rw [← CategoryTheory.comp_apply, ← X.presheaf.map_comp, ← op_comp]
      have : homOfLE (le_top : U ≤ ⊤) ≫ homOfLE htop = homOfLE (le_sup_left : U ≤ U ⊔ V) :=
        Subsingleton.elim _ _
      rw [this, hsU]
    ·
      change X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (X.presheaf.map (homOfLE htop).op s) = c
      rw [← CategoryTheory.comp_apply, ← X.presheaf.map_comp, ← op_comp]
      have : homOfLE (le_top : V ≤ ⊤) ≫ homOfLE htop = homOfLE (le_sup_right : V ≤ U ⊔ V) :=
        Subsingleton.elim _ _
      rw [this, hsV]

private lemma finrank_eq_finrank_appTop
  {Z : (Scheme : Type (u + 1))} [IsAffine Z]
  {R : (CommRingCat : Type (u + 1))}
  (k : Z ⟶ Spec R) [IsFinite k] [Flat k]
  (x : Spec R) :
  -- imply
  k.finrank x = ((Scheme.ΓSpecIso R).inv ≫ k.appTop).hom.finrank x := by
  -- proof
  have hk : k = Z.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ k.appTop) := by
    rw [Spec.map_comp, ← Category.assoc]
    change k = (Z.toSpecΓ ≫ Spec.map k.appTop) ≫ Spec.map (Scheme.ΓSpecIso R).inv
    rw [← Scheme.toSpecΓ_naturality, Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have hk' : Spec.map ((Scheme.ΓSpecIso R).inv ≫ k.appTop) = Z.isoSpec.inv ≫ k :=
    (Iso.eq_inv_comp Z.isoSpec).mpr hk.symm
  let _ : IsFinite (Spec.map ((Scheme.ΓSpecIso R).inv ≫ k.appTop)) := by
    rw [hk']
    infer_instance
  let _ : Flat (Spec.map ((Scheme.ΓSpecIso R).inv ≫ k.appTop)) := by
    rw [hk']
    infer_instance
  have h1 : ((Scheme.ΓSpecIso R).inv ≫ k.appTop).hom.Finite := (IsFinite.SpecMap_iff _).mp inferInstance
  have h2 : ((Scheme.ΓSpecIso R).inv ≫ k.appTop).hom.Flat := Flat.SpecMap_iff.mp inferInstance
  conv_lhs => rw [hk]
  rw [Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_SpecMap_eq_finrank h1 h2]

private lemma finrank_add_affine
  {R : (CommRingCat : Type (u + 1))}
  {Y : (Scheme : Type (u + 1))}
  (h : Y ⟶ Spec R) [IsFinite h] [Flat h] [LocallyOfFinitePresentation h]
  (U V : Y.Opens)
  (x : Spec R)
  -- given
  (hUV : U ⊔ V = ⊤)
  (hdisj : U ⊓ V = ⊥) :
  -- imply
  (U.ι ≫ h).finrank x + (V.ι ≫ h).finrank x = h.finrank x := by
  -- proof
  let _ : IsAffine Y := isAffine_of_isAffineHom h
  have hUc : IsClosed (U : Set Y) := by
    have : (U : Set Y) = (V : Set Y)ᶜ := by
      ext y
      constructor
      ·
        intro hy hy'
        have : y ∈ U ⊓ V := ⟨hy, hy'⟩
        rw [hdisj] at this
        apply this
      ·
        intro hy
        have : y ∈ U ⊔ V := by
          rw [hUV]
          trivial
        obtain h | h := this
        · apply h
        · apply absurd h hy
    rw [this, isClosed_compl_iff]
    apply V.isOpen
  have hVc : IsClosed (V : Set Y) := by
    have : (V : Set Y) = (U : Set Y)ᶜ := by
      ext y
      constructor
      ·
        intro hy hy'
        have : y ∈ U ⊓ V := ⟨hy', hy⟩
        rw [hdisj] at this
        apply this
      ·
        intro hy
        have : y ∈ U ⊔ V := by
          rw [hUV]
          trivial
        obtain h | h := this
        · apply absurd h hy
        · apply h
    rw [this, isClosed_compl_iff]
    apply U.isOpen
  have hUcRange : IsClosed (Set.range U.ι.base) := by
    rw [Scheme.Opens.range_ι]
    apply hUc
  have hVcRange : IsClosed (Set.range V.ι.base) := by
    rw [Scheme.Opens.range_ι]
    apply hVc
  let _ : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion _ hUcRange
  let _ : IsClosedImmersion V.ι := IsClosedImmersion.of_isPreimmersion _ hVcRange
  let _ : IsAffine (U : (Scheme : Type (u + 1))) := isAffine_of_isAffineHom (U.ι ≫ h)
  let _ : IsAffine (V : (Scheme : Type (u + 1))) := isAffine_of_isAffineHom (V.ι ≫ h)
  rw [finrank_eq_finrank_appTop h, finrank_eq_finrank_appTop (U.ι ≫ h), finrank_eq_finrank_appTop (V.ι ≫ h)]
  set φ : RingHom R (Y.presheaf.obj (op ⊤)) := ((Scheme.ΓSpecIso R).inv ≫ h.appTop).hom
  have hU' : ((Scheme.ΓSpecIso R).inv ≫ (U.ι ≫ h).appTop).hom = U.ι.appTop.hom.comp φ := rfl
  have hV' : ((Scheme.ΓSpecIso R).inv ≫ (V.ι ≫ h).appTop).hom = V.ι.appTop.hom.comp φ := rfl
  rw [hU', hV']
  have hsurj : Function.Surjective (Scheme.ΓSpecIso R).inv.hom := by
    intro y
    refine ⟨(Scheme.ΓSpecIso R).hom y, ?_⟩
    change ((Scheme.ΓSpecIso R).hom ≫ (Scheme.ΓSpecIso R).inv) y = y
    rw [Iso.hom_inv_id]
    rfl
  have hbijι : Function.Bijective (Scheme.ΓSpecIso R).inv.hom :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv
  have h₁fin : (U.ι.appTop.hom.comp φ).Finite := by
    rw [← hU']
    apply ((U.ι ≫ h).finite_appTop).comp (RingHom.Finite.of_surjective _ hsurj)
  have h₁flat : (U.ι.appTop.hom.comp φ).Flat := by
    rw [← hU']
    apply (RingHom.Flat.of_bijective hbijι).comp (U.ι ≫ h).flat_appTop
  have h₂fin : (V.ι.appTop.hom.comp φ).Finite := by
    rw [← hV']
    apply ((V.ι ≫ h).finite_appTop).comp (RingHom.Finite.of_surjective _ hsurj)
  have h₂flat : (V.ι.appTop.hom.comp φ).Flat := by
    rw [← hV']
    apply (RingHom.Flat.of_bijective hbijι).comp (V.ι ≫ h).flat_appTop
  have hbij : Function.Bijective (RingHom.prod U.ι.appTop.hom V.ι.appTop.hom) := by
    have hUV' : (Scheme.Hom.opensFunctor U.ι).obj ⊤ ⊔ (Scheme.Hom.opensFunctor V.ι).obj ⊤ = ⊤ := by
      rw [Scheme.Opens.ι_image_top, Scheme.Opens.ι_image_top, hUV]
    have hdisj' : (Scheme.Hom.opensFunctor U.ι).obj ⊤ ⊓ (Scheme.Hom.opensFunctor V.ι).obj ⊤ = ⊥ := by
      rw [Scheme.Opens.ι_image_top, Scheme.Opens.ι_image_top, hdisj]
    refine bijective_restrict_prod ((Scheme.Hom.opensFunctor U.ι).obj ⊤) ((Scheme.Hom.opensFunctor V.ι).obj ⊤) hUV' hdisj'
  refine finrank_add_of_bijective_prod φ U.ι.appTop.hom V.ι.appTop.hom hbij h₁fin h₁flat h₂fin h₂flat x

/--
[AlgebraicGeometry_Scheme_Hom_finrank_restrict_add_finrank_restrict_of_isCompl](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_finrank_restrict_add_finrank_restrict_of_isCompl.lean)
-/
@[path]
private lemma main
  {Y S : (Scheme : Type (u + 1))}
  (f : Y ⟶ S) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]
  (U V : Y.Opens)
  (s : S)
  -- given
  (hUV : U ⊔ V = ⊤)
  (hdisj : U ⊓ V = ⊥) :
  -- imply
  (U.ι ≫ f).finrank s + (V.ι ≫ f).finrank s = f.finrank s := by
  -- proof
  have hUc : IsClosed (U : Set Y) := by
    have : (U : Set Y) = (V : Set Y)ᶜ := by
      ext y
      constructor
      ·
        intro hy hy'
        have : y ∈ U ⊓ V := ⟨hy, hy'⟩
        rw [hdisj] at this
        apply this
      ·
        intro hy
        have : y ∈ U ⊔ V := by
          rw [hUV]
          trivial
        obtain h | h := this
        · apply h
        · apply absurd h hy
    rw [this, isClosed_compl_iff]
    apply V.isOpen
  have hVc : IsClosed (V : Set Y) := by
    have : (V : Set Y) = (U : Set Y)ᶜ := by
      ext y
      constructor
      ·
        intro hy hy'
        have : y ∈ U ⊓ V := ⟨hy', hy⟩
        rw [hdisj] at this
        apply this
      ·
        intro hy
        have : y ∈ U ⊔ V := by
          rw [hUV]
          trivial
        obtain h | h := this
        · apply absurd h hy
        · apply h
    rw [this, isClosed_compl_iff]
    apply U.isOpen
  have hUcRange : IsClosed (Set.range U.ι.base) := by
    rw [Scheme.Opens.range_ι]
    apply hUc
  have hVcRange : IsClosed (Set.range V.ι.base) := by
    rw [Scheme.Opens.range_ι]
    apply hVc
  let _ : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion _ hUcRange
  let _ : IsClosedImmersion V.ι := IsClosedImmersion.of_isPreimmersion _ hVcRange
  obtain ⟨R, g, hg, s', rfl⟩ := S.exists_Spec_apply_eq s
  have sqY : IsPullback (pullback.fst f g) (pullback.snd f g) f g := IsPullback.of_hasPullback f g
  have sqU := (isPullback_morphismRestrict (pullback.fst f g) U).paste_vert sqY
  have sqV := (isPullback_morphismRestrict (pullback.fst f g) V).paste_vert sqY
  rw [← Scheme.Hom.finrank_of_isPullback _ _ _ _ sqY s', ← Scheme.Hom.finrank_of_isPullback _ _ _ _ sqU s', ← Scheme.Hom.finrank_of_isPullback _ _ _ _ sqV s']
  apply finrank_add_affine (pullback.snd f g)
  · rw [← Scheme.Hom.preimage_sup, hUV, Scheme.Hom.preimage_top]
  · rw [← Scheme.Hom.preimage_inf, hdisj, Scheme.Hom.preimage_bot]


-- created on 2026-10-20
