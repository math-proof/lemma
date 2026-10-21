import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma rank_baseChange_eq
  {A : Type u} (B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [Nontrivial B] (N : Type u) [AddCommGroup N] [Module A N] [Module.Free A N] :
  Module.rank B (B ⊗[A] N) = Module.rank A N := by
  let _ : Nontrivial A := (algebraMap A B).domain_nontrivial
  let b := Module.Free.chooseBasis A N
  let b' := Algebra.TensorProduct.basis B b
  rw [← b.mk_eq_rank'', ← b'.mk_eq_rank'']
private lemma rank_eq_of_equiv
  {A : Type u} [CommRing A] {M N : Type u} [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N] (e : M ≃ₗ[A] N) :
  Module.rank A M = Module.rank A N :=
  e.rank_eq
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
private noncomputable def omegaLocEquiv
  (T' : Type u) [CommRing T'] [Algebra T T'] [Algebra R T'] [IsScalarTower R T T']
  (M : Submonoid T) [IsLocalization M T'] :
  (KaehlerDifferential R T') ≃ₗ[T'] T' ⊗[T] (KaehlerDifferential R T) :=
  let _ : Algebra.FormallyEtale T T' := Algebra.FormallyEtale.of_isLocalization M
  (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R T T').symm
private lemma isStandardSmoothOfRelativeDimension_of_faithfullyFlat
  {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  [Module.FaithfullyFlat R S] (n : ℕ)
    (hloc : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap S (S ⊗[R] T)))
    (Tt : Type u) [CommRing Tt] [Algebra T Tt] [Algebra R Tt] [IsScalarTower R T Tt] (t : T)
    [IsLocalization.Away t Tt] [Nontrivial Tt] [Algebra.IsStandardSmooth R Tt] :
    Algebra.IsStandardSmoothOfRelativeDimension n R Tt := by
  classical
  rw [Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth]
  let _ : Algebra T (S ⊗[R] T) := Algebra.TensorProduct.rightAlgebra
  let _ : Nontrivial (S ⊗[R] Tt) := by
    rw [Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right]; infer_instance
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal (S ⊗[R] Tt)
  let φ : S ⊗[R] T →ₐ[S] S ⊗[R] Tt :=
    Algebra.TensorProduct.map (AlgHom.id S S) (IsScalarTower.toAlgHom R T Tt)
  let 𝔮 : Ideal (S ⊗[R] T) := 𝔪.comap φ
  let h𝔮 : 𝔮.IsPrime := Ideal.comap_isPrime φ 𝔪
  have ha : ((1 : S) ⊗ₜ[R] t : S ⊗[R] T) ∉ 𝔮 := by
    intro h
    have hu : IsUnit (φ ((1 : S) ⊗ₜ[R] t)) := by
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.coe_toAlgHom']
      exact ((IsLocalization.Away.algebraMap_isUnit t).map
        (Algebra.TensorProduct.includeRight : Tt →ₐ[R] S ⊗[R] Tt))
    refine h𝔪.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
  obtain ⟨sA, hsA, hP⟩ := hloc
  obtain ⟨u, hu, hu𝔮⟩ : ∃ u ∈ sA, u ∉ 𝔮 := by
    by_contra hcon
    push Not at hcon
    have : Ideal.span sA ≤ 𝔮 := Iff.mpr Ideal.span_le hcon
    rw [hsA, top_le_iff] at this
    apply h𝔮.ne_top this
  let Au := Localization.Away u
  let C := Localization.AtPrime 𝔮
  have hAu : Algebra.IsStandardSmoothOfRelativeDimension n S Au := by
    have := hP u hu
    rwa [← IsScalarTower.algebraMap_eq (R := S) (S := S ⊗[R] T) (A := Au),
      RingHom.isStandardSmoothOfRelativeDimension_algebraMap] at this
  let _ : Algebra.IsStandardSmooth S Au := hAu.isStandardSmooth
  have hCt : IsUnit (algebraMap T C t) := by
    rw [IsScalarTower.algebraMap_apply T (S ⊗[R] T) C]
    exact IsLocalization.map_units C (⟨(1 : S) ⊗ₜ[R] t, ha⟩ : 𝔮.primeCompl)
  have hCu : IsUnit (algebraMap (S ⊗[R] T) C u) := IsLocalization.map_units C (⟨u, hu𝔮⟩ : 𝔮.primeCompl)
  let algTtC : Algebra Tt C := (IsLocalization.Away.lift t hCt).toAlgebra
  let _ : IsScalarTower T Tt C := IsScalarTower.of_algebraMap_eq fun x =>
    (IsLocalization.Away.lift_eq t hCt x).symm
  let algAuC : Algebra Au C := (IsLocalization.Away.lift u hCu).toAlgebra
  let _ : IsScalarTower (S ⊗[R] T) Au C := IsScalarTower.of_algebraMap_eq fun x =>
    (IsLocalization.Away.lift_eq u hCu x).symm
  let _ : IsScalarTower T Au C := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply T (S ⊗[R] T) Au, IsScalarTower.algebraMap_apply T (S ⊗[R] T) C,
      ← IsScalarTower.algebraMap_apply (S ⊗[R] T) Au C]
  let _ : Nontrivial Au := (algebraMap Au C).domain_nontrivial
  have eT : (KaehlerDifferential R Tt) ≃ₗ[Tt] Tt ⊗[T] (KaehlerDifferential R T) := omegaLocEquiv (R := R) Tt (Submonoid.powers t)
  have eA : KaehlerDifferential S (S ⊗[R] T) ≃ₗ[S ⊗[R] T] (S ⊗[R] T) ⊗[T] (KaehlerDifferential R T) :=
    (KaehlerDifferential.tensorKaehlerEquiv R S T (S ⊗[R] T)).symm
  let _ : Algebra.FormallyEtale (S ⊗[R] T) Au := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers u)
  have eAu : (KaehlerDifferential S Au) ≃ₗ[Au] Au ⊗[T] (KaehlerDifferential R T) :=
    ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale S (S ⊗[R] T) Au).symm.trans
      ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl Au Au) eA).trans
        (TensorProduct.AlgebraTensorModule.cancelBaseChange T (S ⊗[R] T) Au Au (KaehlerDifferential R T))))
  have e1 : C ⊗[T] (KaehlerDifferential R T) ≃ₗ[C] C ⊗[Tt] (KaehlerDifferential R Tt) :=
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange T Tt C C (KaehlerDifferential R T)).symm.trans
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl C C) eT.symm))
  have e2 : C ⊗[T] (KaehlerDifferential R T) ≃ₗ[C] C ⊗[Au] (KaehlerDifferential S Au) :=
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange T Au C C (KaehlerDifferential R T)).symm.trans
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl C C) eAu.symm))
  have h1 : Module.rank C (C ⊗[Tt] (KaehlerDifferential R Tt)) = Module.rank Tt (KaehlerDifferential R Tt) := rank_baseChange_eq C (KaehlerDifferential R Tt)
  have h2 : Module.rank C (C ⊗[Au] (KaehlerDifferential S Au)) = Module.rank Au (KaehlerDifferential S Au) := rank_baseChange_eq C (KaehlerDifferential S Au)
  have h3 : Module.rank Au (KaehlerDifferential S Au) = n := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n
  rw [← h1, ← e1.rank_eq, e2.rank_eq, h2, h3]
private lemma nontrivial_localization_away
  {T : Type u} [CommRing T] {t : T} (ht : ¬ IsNilpotent t) :
  Nontrivial (Localization.Away t) := by
  by_contra h
  have hs : Subsingleton (Localization.Away t) := by
    rw [← not_nontrivial_iff_subsingleton]
    apply h
  have h01 : algebraMap T (Localization.Away t) 1 = algebraMap T (Localization.Away t) 0 := hs.elim _ _
  obtain ⟨c, hc⟩ := Iff.mp (IsLocalization.eq_iff_exists (Submonoid.powers t) _) h01
  obtain ⟨m, hm⟩ := c.2
  apply ht
  refine ⟨m, ?_⟩
  have hm' : t ^ m = (c : T) := hm
  rw [hm']
  simpa using hc
private lemma span_not_isNilpotent_eq_top
  {T : Type u} [CommRing T] {s : Set T} (hs : Ideal.span s = ⊤) :
  Ideal.span {t ∈ s | ¬ IsNilpotent t} = ⊤ := by
  rw [← Ideal.radical_eq_top, eq_top_iff, ← hs]
  refine Ideal.span_le.mpr fun t ht => ?_
  if hn : IsNilpotent t then
    obtain ⟨m, hm⟩ := hn
    refine ⟨m, ?_⟩
    rw [hm]
    apply Ideal.zero_mem
  else
    apply Ideal.le_radical
    apply Ideal.subset_span
    exact ⟨ht, hn⟩
private lemma codescendsAlong
  (n : ℕ) :
  RingHom.CodescendsAlong (fun {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) => RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) f) (fun {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) => RingHom.FaithfullyFlat f) := by
  refine RingHom.CodescendsAlong.mk _
    (RingHom.locally_respectsIso RingHom.isStandardSmoothOfRelativeDimension_respectsIso) ?_
  intro R S T _ _ _ _ _ h h'
  let _ : Module.FaithfullyFlat R S := by
    rw [← RingHom.faithfullyFlat_algebraMap_iff]
    apply h
  have hsm : Algebra.Smooth R T := by
    have hST : (algebraMap S (S ⊗[R] T)).Smooth := by
      rw [RingHom.smooth_iff_locally_isStandardSmooth]
      apply RingHom.locally_of_locally
        (fun {R' S' : Type u} [CommRing R'] [CommRing S'] (f : R' →+* S')
          (hf : RingHom.IsStandardSmoothOfRelativeDimension n f) =>
          RingHom.IsStandardSmoothOfRelativeDimension.isStandardSmooth n f hf) h'
    rw [RingHom.smooth_algebraMap] at hST
    apply Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat S
  have hls : RingHom.Locally RingHom.IsStandardSmooth (algebraMap R T) := by
    rwa [← RingHom.smooth_iff_locally_isStandardSmooth, RingHom.smooth_algebraMap]
  obtain ⟨s, hs, hstd⟩ := hls
  refine ⟨{t ∈ s | ¬ IsNilpotent t}, span_not_isNilpotent_eq_top hs, ?_⟩
  intro t ht
  let _ : Nontrivial (Localization.Away t) := nontrivial_localization_away ht.2
  have h1 := hstd t ht.1
  rw [← IsScalarTower.algebraMap_eq (R := R) (S := T) (A := Localization.Away t)] at h1 ⊢
  rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  let _ : Algebra.IsStandardSmooth R (Localization.Away t) := by
    rw [← RingHom.isStandardSmooth_algebraMap]
    apply h1
  apply isStandardSmoothOfRelativeDimension_of_faithfullyFlat n h' (Localization.Away t) t
/--
[AlgebraicGeometry_SmoothOfRelativeDimension_of_isPullback_of_flat_of_surjective](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_SmoothOfRelativeDimension_of_isPullback_of_flat_of_surjective.lean)
-/
@[path]
private lemma main
  (n : ℕ)
  {P X Y Z : (Scheme : Type (u + 1))} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (H : IsPullback fst snd f g) [Flat f] [Surjective f] [QuasiCompact f]
    [SmoothOfRelativeDimension n fst] : SmoothOfRelativeDimension n g := by
  let _ : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension n) :=
    smoothOfRelativeDimension_isStableUnderBaseChange n
  let _ : MorphismProperty.DescendsAlong (@SmoothOfRelativeDimension n) (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
    HasRingHomProperty.descendsAlong_flat (codescendsAlong n)
  apply MorphismProperty.of_isPullback_of_descendsAlong (P := @SmoothOfRelativeDimension n)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) H ⟨⟨‹_›, ‹_›⟩, ‹_›⟩ ‹_›


-- created on 2026-10-20
