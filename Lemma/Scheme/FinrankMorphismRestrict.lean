import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma finrank_tensorProduct_eq_of_algEquiv
  [CommRing A] [CommRing R] [CommRing R'] [Algebra A R] [Algebra A R']
  (e : AlgEquiv A R R')
  (M : Type*) [AddCommGroup M] [Module A M] :
  -- imply
  Module.finrank R (TensorProduct A R M) = Module.finrank R' (TensorProduct A R' M) := by
  -- proof
  let j : LinearEquiv (RingHom.id A) (TensorProduct A R M) (TensorProduct A R' M) :=
    TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl A M)
  have hc : ∀ (r : R) (x : TensorProduct A R M), j (r • x) = e r • j x := by
    intro r x
    refine TensorProduct.inductionOn x ?_ ?_
    ·
      intro s m
      simp only [j, TensorProduct.smul_tmul', smul_eq_mul, TensorProduct.congr_tmul, LinearEquiv.refl_apply, AlgEquiv.toLinearEquiv_apply, map_mul]
    ·
      intro x y hx hy
      simp only [smul_add, map_add, hx, hy]
  have h := lift_rank_eq_of_equiv_equiv e j.toAddEquiv e.bijective hc
  have h' := congrArg Cardinal.toNat h
  simpa [Module.finrank, Cardinal.toNat_lift] using h'

private lemma rankAtStalk_eq_of_isLocalizedModule
  [CommRing A] [CommRing A'] [Algebra A A']
  [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M'] [Module A' M'] [IsScalarTower A A' M']
  (S : Submonoid A) [IsLocalization S A']
  (f : LinearMap (RingHom.id A) M M') [IsLocalizedModule S f]
  (p : PrimeSpectrum A') :
  -- imply
  Module.rankAtStalk (R := A') M' p = Module.rankAtStalk (R := A) M (p.comap (algebraMap A A')) := by
  -- proof
  rw [Module.rankAtStalk_eq_finrank_tensorProduct, Module.rankAtStalk_eq_finrank_tensorProduct]
  let _ : IsLocalization.AtPrime (Localization.AtPrime p.asIdeal) (p.comap (algebraMap A A')).asIdeal :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (M := S) (Localization.AtPrime p.asIdeal) p.asIdeal
  let e : AlgEquiv A (Localization.AtPrime (p.comap (algebraMap A A')).asIdeal) (Localization.AtPrime p.asIdeal) :=
    IsLocalization.algEquiv (p.comap (algebraMap A A')).asIdeal.primeCompl _ _
  rw [finrank_tensorProduct_eq_of_algEquiv e M]
  have hb : IsBaseChange A' f := (isLocalizedModule_iff_isBaseChange S A' f).mp inferInstance
  let e₁ : LinearEquiv (RingHom.id (Localization.AtPrime p.asIdeal)) (TensorProduct A' (Localization.AtPrime p.asIdeal) M') (TensorProduct A' (Localization.AtPrime p.asIdeal) (TensorProduct A A' M)) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _) hb.equiv.symm
  let e₂ := TensorProduct.AlgebraTensorModule.cancelBaseChange A A' (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) M
  apply (e₁.trans e₂).finrank_eq

private lemma finrank_eq_of_isPushout_of_away
  {R B T P : (CommRingCat : Type (u + 1))}
  {φ : R ⟶ B}
  {ψ : R ⟶ T}
  {inl : B ⟶ P}
  {inr : T ⟶ P}
  (r : R)
  -- given
  (h : IsPushout φ ψ inl inr)
  (hT : let _ := ψ.hom.toAlgebra; IsLocalization.Away r T)
  (x : PrimeSpectrum T) :
  -- imply
  inr.hom.finrank x = φ.hom.finrank (PrimeSpectrum.comap ψ.hom x) := by
  -- proof
  algebraize [φ.hom, ψ.hom, inl.hom, inr.hom, inl.hom.comp φ.hom]
  have : IsScalarTower R T P := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom h.1.1)
  have : Algebra.IsPushout R B T P := CommRingCat.isPushout_iff_isPushout.mp h
  have : Algebra.IsPushout R T B P := Algebra.IsPushout.symm inferInstance
  have hbc : IsBaseChange T (IsScalarTower.toAlgHom R B P).toLinearMap := Algebra.IsPushout.out
  let _ : IsLocalization.Away r T := hT
  let _ : IsLocalizedModule (Submonoid.powers r) (IsScalarTower.toAlgHom R B P).toLinearMap :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers r) T _).mpr hbc
  change Module.rankAtStalk (R := T) P x = Module.rankAtStalk (R := R) B _
  apply rankAtStalk_eq_of_isLocalizedModule (Submonoid.powers r) (IsScalarTower.toAlgHom R B P).toLinearMap x

/--
[AlgebraicGeometry_Scheme_Hom_finrank_morphismRestrict_eq_finrank](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_finrank_morphismRestrict_eq_finrank.lean)
-/
@[path]
private lemma main
  {X S : (Scheme : Type (u + 1))}
  (f : X ⟶ S) [IsFinite f]
  (W : S.Opens) [Flat (morphismRestrict f W)]
  (s : S)
  -- given
  (hs : s ∈ W) :
  -- imply
  (morphismRestrict f W).finrank ⟨s, hs⟩ = f.finrank s := by
  -- proof
  classical
  set i₀ := S.affineOpenCover.idx s
  set T : (Scheme : Type (u + 1)) := Spec (S.affineOpenCover.X i₀)
  set ι : T ⟶ S := S.affineOpenCover.f i₀
  set t₀ : T := (S.affineOpenCover.covers s).choose
  have ht₀ : ι t₀ = s := (S.affineOpenCover.covers s).choose_spec
  set g : pullback f ι ⟶ T := pullback.snd f ι
  have hdef : f.finrank s = g.appTop.hom.finrank (T.isoSpec.hom t₀) := rfl
  have ht₀W : t₀ ∈ ((TopologicalSpace.Opens.map ι.base).obj W) := by
    change ι t₀ ∈ W
    rw [ht₀]
    apply hs
  obtain ⟨r, hr, ht₀r⟩ := (isAffineOpen_top T).exists_basicOpen_le ⟨t₀, ht₀W⟩ (Set.mem_univ _)
  set T' : (Scheme : Type (u + 1)) := ↑(T.basicOpen r)
  set j : T' ⟶ T := (T.basicOpen r).ι
  let _ : IsAffine T' := (isAffineOpen_top T).basicOpen r
  set t' : T' := ⟨t₀, ht₀r⟩
  have hjt' : j t' = t₀ := rfl
  set g' : pullback g j ⟶ T' := pullback.snd g j
  let _ : IsAffine (pullback f ι) := isAffine_of_isAffineHom g
  let _ : IsAffine (pullback g j) := isAffine_of_isAffineHom g'
  have hrange : Set.range (j ≫ ι).base ⊆ Set.range W.ι.base := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    apply hr x.2
  set k : T' ⟶ ↑W := IsOpenImmersion.lift W.ι (j ≫ ι) hrange
  have hkfac : k ≫ W.ι = j ≫ ι := IsOpenImmersion.lift_fac _ _ _
  have hkt' : k t' = ⟨s, hs⟩ := by
    apply W.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hkfac, Scheme.Hom.comp_apply, hjt', ht₀]
    rfl
  have big : IsPullback (pullback.fst g j ≫ pullback.fst f ι) g' f (k ≫ W.ι) := by
    rw [hkfac]
    apply (IsPullback.of_hasPullback g j).paste_horiz (IsPullback.of_hasPullback f ι)
  have hP := IsPullback.of_right' big (isPullback_morphismRestrict f W).flip
  let _ : Flat g' := MorphismProperty.of_isPullback (P := @Flat) hP inferInstance
  let _ : IsFinite g' := MorphismProperty.of_isPullback (P := @IsFinite) hP inferInstance
  have h1 : (morphismRestrict f W).finrank ⟨s, hs⟩ = g'.finrank t' := by
    rw [← hkt']
    apply (Scheme.Hom.finrank_of_isPullback _ _ _ _ hP t').symm
  have h2 : g'.finrank t' = g'.appTop.hom.finrank (T'.isoSpec.hom t') := by
    have sq : IsPullback (pullback g j).isoSpec.hom g' (Spec.map g'.appTop) T'.isoSpec.hom :=
      IsPullback.of_horiz_isIso ⟨Scheme.isoSpec_hom_naturality g'⟩
    have hfin : g'.appTop.hom.Finite := g'.finite_appTop
    have hflat : g'.appTop.hom.Flat := HasRingHomProperty.appTop (P := @Flat) (f := g') inferInstance
    let _ : IsFinite (Spec.map g'.appTop) := (IsFinite.SpecMap_iff _).mpr hfin
    let _ : Flat (Spec.map g'.appTop) := (HasRingHomProperty.Spec_iff (P := @Flat)).mpr hflat
    rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ sq t', Scheme.Hom.finrank_SpecMap_eq_finrank hfin hflat]
  have h3 : g'.appTop.hom.finrank (T'.isoSpec.hom t') = g.appTop.hom.finrank (T.isoSpec.hom t₀) := by
    have hpo : IsPushout g.appTop j.appTop (pullback.fst g j).appTop g'.appTop :=
      isPushout_appTop_of_isPullback (IsPullback.of_hasPullback g j)
    have hloc : let _ := j.appTop.hom.toAlgebra; IsLocalization.Away r (T'.presheaf.obj (op ⊤)) :=
      AlgebraicGeometry.Γ_restrict_isLocalization T r
    rw [finrank_eq_of_isPushout_of_away r hpo hloc]
    congr 1
    change (Spec.map j.appTop) (T'.isoSpec.hom t') = T.isoSpec.hom t₀
    rw [← Scheme.Hom.comp_apply, Scheme.isoSpec_hom_naturality, Scheme.Hom.comp_apply, hjt']
  rw [h1, h2, h3, hdef]


-- created on 2026-10-20
