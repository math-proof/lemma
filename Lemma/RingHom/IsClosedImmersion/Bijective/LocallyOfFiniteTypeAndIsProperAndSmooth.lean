import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma surjective_specMap_of_surjective_of_isNilpotent_ker
  {P B' : Type} [CommRing P] [CommRing B']
  (π : P →+* B')
  -- given
  (hπs : Function.Surjective π)
  (hπn : IsNilpotent (RingHom.ker π)) :
  -- imply
  Surjective (Spec.map (CommRingCat.ofHom π)) := by
  -- proof
  refine ⟨(PrimeSpectrum.isHomeomorph_comap π (fun x => ⟨1, Nat.one_pos, ?_⟩) ?_).surjective⟩
  ·
    obtain ⟨y, hy⟩ := hπs x
    exact ⟨y, by rwa [pow_one]⟩
  ·
    intro x hx
    rw [mem_nilradical]
    obtain ⟨n, hn⟩ := hπn
    refine ⟨n, ?_⟩
    have : x ^ n ∈ RingHom.ker π ^ n := Ideal.pow_mem_pow hx n
    rw [hn] at this
    simpa using this
private lemma gamma0
  {P B' : Type} [CommRing P] [CommRing B']
  (π : P →+* B')
  (hπs : Function.Surjective π)
  (hπn : IsNilpotent (RingHom.ker π))
  {X X' : (Scheme : Type 1)}
  (f : X ⟶ Spec (CommRingCat.of P))
  (f' : X' ⟶ Spec (CommRingCat.of B'))
  (k' : X' ⟶ X)
  (hk : IsPullback k' f' f (Spec.map (CommRingCat.ofHom π))) :
  -- imply
  IsClosedImmersion k' ∧ Function.Bijective k'.base := by
  -- proof
  have h1 : IsClosedImmersion k' :=
    MorphismProperty.of_isPullback hk.flip (IsClosedImmersion.spec_of_surjective _ hπs)
  refine ⟨h1, h1.isClosedEmbedding.injective,
    (MorphismProperty.of_isPullback hk.flip (surjective_specMap_of_surjective_of_isNilpotent_ker π hπs hπn)).1⟩
private lemma finiteType_of_finiteType_baseChange_of_surjective_of_isNilpotent_ker
  [CommRing P] [CommRing B'] [CommRing A] [Algebra P B'] [Algebra P A]
  -- given
  (hπs : Function.Surjective (algebraMap P B'))
  (hπn : IsNilpotent (RingHom.ker (algebraMap P B')))
  (h : (Algebra.TensorProduct.includeRight (R := P) (A := A) (B := B')).toRingHom.FiniteType) :
  -- imply
  Algebra.FiniteType P A := by
  -- proof
  classical
  set J : Ideal P := RingHom.ker (algebraMap P B') with hJdef
  let ι : A →ₐ[P] A ⊗[P] B' := Algebra.TensorProduct.includeLeft
  have hιs : Function.Surjective ι := by
    intro x
    refine TensorProduct.inductionOn x ?_ ?_
    ·
      intro a b
      obtain ⟨p, rfl⟩ := hπs b
      refine ⟨p • a, ?_⟩
      change TensorProduct.tmul P (p • a) (1 : B') = TensorProduct.tmul P a (algebraMap P B' p)
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, TensorProduct.tmul_smul]
    ·
      intro x y hx hy
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, ha, hb]⟩
  let JA : Ideal A := J.map (algebraMap P A)
  have hker : ∀ a : A, ι a = 0 → a ∈ JA := by
    let e : (P ⧸ J) ≃ₐ[P] B' := Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId P B') hπs
    let g : (P ⧸ J) →ₐ[P] A ⧸ JA := Ideal.quotientMapₐ JA (Algebra.ofId P A) Ideal.le_comap_map
    let fB : B' →ₐ[P] A ⧸ JA := g.comp e.symm.toAlgHom
    let β : A ⊗[P] B' →ₐ[P] A ⧸ JA :=
      Algebra.TensorProduct.lift (Ideal.Quotient.mkₐ P JA) fB (fun _ _ => mul_comm _ _)
    intro a ha
    have hβ : β (ι a) = Ideal.Quotient.mk JA a := by
      change β (TensorProduct.tmul P a (1 : B')) = _
      rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
      rfl
    rw [ha, map_zero] at hβ
    apply Iff.mp Ideal.Quotient.eq_zero_iff_mem hβ.symm
  let instB : Algebra B' (A ⊗[P] B') :=
    (Algebra.TensorProduct.includeRight (R := P) (A := A) (B := B')).toRingHom.toAlgebra
  have hFT : Algebra.FiniteType B' (A ⊗[P] B') := h
  obtain ⟨T, hT⟩ := hFT.out
  choose s hs using fun t : A ⊗[P] B' => hιs t
  let S : Subalgebra P A := Algebra.adjoin P (s '' (T : Set (A ⊗[P] B')))
  have hS' : ∀ x : A ⊗[P] B', ∃ a ∈ S, ι a = x := by
    let S' : Subalgebra B' (A ⊗[P] B') :=
      { carrier := {x | ∃ a ∈ S, ι a = x}
        mul_mem' := by
          rintro x y ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
          exact ⟨a * b, S.mul_mem ha hb, map_mul _ _ _⟩
        add_mem' := by
          rintro x y ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
          exact ⟨a + b, S.add_mem ha hb, map_add _ _ _⟩
        algebraMap_mem' := by
          intro b
          obtain ⟨p, rfl⟩ := hπs b
          refine ⟨p • 1, S.smul_mem S.one_mem p, ?_⟩
          change TensorProduct.tmul P (p • (1 : A)) (1 : B') = TensorProduct.tmul P (1 : A) (algebraMap P B' p)
          rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, TensorProduct.tmul_smul] }
    have hle : Algebra.adjoin B' (T : Set (A ⊗[P] B')) ≤ S' := by
      refine Algebra.adjoin_le ?_
      intro t ht
      exact ⟨s t, Algebra.subset_adjoin ⟨t, ht, rfl⟩, hs t⟩
    intro x
    apply hle
    rw [hT]
    apply Algebra.mem_top
  have h1 : (⊤ : Submodule P A) ≤ S.toSubmodule ⊔ J • (⊤ : Submodule P A) := by
    intro a _
    obtain ⟨b, hb, hba⟩ := hS' (ι a)
    have hmem : a - b ∈ JA := hker (a - b) (by rw [map_sub, hba, sub_self])
    have hmem' : a - b ∈ J • (⊤ : Submodule P A) := by
      rwa [Ideal.smul_top_eq_map]
    have : a = b + (a - b) := by ring
    rw [this]
    apply Submodule.add_mem_sup hb hmem'
  have h2 : ∀ n : ℕ, (⊤ : Submodule P A) ≤ S.toSubmodule ⊔ J ^ n • (⊤ : Submodule P A) := by
    intro n
    induction n
    ·
      rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
      apply le_sup_right
    ·
      rename_i n ih
      calc
        _ ≤ S.toSubmodule ⊔ J ^ n • (⊤ : Submodule P A) := ih
        _ ≤ S.toSubmodule ⊔ J ^ n • (S.toSubmodule ⊔ J • (⊤ : Submodule P A)) :=
          sup_le_sup_left (Submodule.smul_mono le_rfl h1) _
        _ = S.toSubmodule ⊔ (J ^ n • S.toSubmodule ⊔ J ^ (n + 1) • (⊤ : Submodule P A)) := by
          rw [Submodule.smul_sup, ← Submodule.mul_smul, ← pow_succ]
        _ ≤ S.toSubmodule ⊔ J ^ (n + 1) • (⊤ : Submodule P A) :=
          sup_le le_sup_left (sup_le (le_sup_left.trans' Submodule.smul_le_right) le_sup_right)
  obtain ⟨N, hN⟩ := hπn
  have hN' : J ^ N = ⊥ := hN
  refine ⟨⟨T.image s, ?_⟩⟩
  rw [Finset.coe_image]
  rw [eq_top_iff]
  intro a _
  have := h2 N (Submodule.mem_top : a ∈ (⊤ : Submodule P A))
  rwa [hN', Submodule.bot_smul, sup_bot_eq] at this
private lemma locallyOfFiniteType_specMap_of_pullback_snd
  {P B' : Type} [CommRing P] [CommRing B']
  (π : P →+* B')
  (hπs : Function.Surjective π)
  (hπn : IsNilpotent (RingHom.ker π))
  {R : (CommRingCat : Type 1)}
  (ψ : CommRingCat.of P ⟶ R)
  (h : LocallyOfFiniteType (pullback.snd (Spec.map ψ) (Spec.map (CommRingCat.ofHom π)))) :
  -- imply
  LocallyOfFiniteType (Spec.map ψ) := by
  -- proof
  let algR : Algebra P R := ψ.hom.toAlgebra
  let algB : Algebra P B' := π.toAlgebra
  have h' : LocallyOfFiniteType (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap P R)))
      (Spec.map (CommRingCat.ofHom (algebraMap P B')))) := h
  rw [← pullbackSpecIso_hom_snd P R B',
    MorphismProperty.cancel_left_of_respectsIso (P := @LocallyOfFiniteType),
    HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h'
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  apply finiteType_of_finiteType_baseChange_of_surjective_of_isNilpotent_ker hπs hπn h'
private lemma gamma1
  {P B' : Type} [CommRing P] [CommRing B']
  (π : P →+* B')
  (hπs : Function.Surjective π)
  (hπn : IsNilpotent (RingHom.ker π))
  {X X' : (Scheme : Type 1)}
  (f : X ⟶ Spec (CommRingCat.of P))
  (f' : X' ⟶ Spec (CommRingCat.of B'))
  (k' : X' ⟶ X)
  (hk : IsPullback k' f' f (Spec.map (CommRingCat.ofHom π)))
  (hft : LocallyOfFiniteType f') :
  -- imply
  LocallyOfFiniteType f := by
  -- proof
  let _ : LocallyOfFiniteType (pullback.snd f (Spec.map (CommRingCat.ofHom π))) := by
    rw [← hk.isoPullback_inv_snd]
    infer_instance
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFiniteType) X.affineCover]
  intro i
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (X.affineCover.f i ≫ f)
  have h2 : LocallyOfFiniteType (pullback.snd (X.affineCover.f i)
      (pullback.fst f (Spec.map (CommRingCat.ofHom π))) ≫ pullback.snd f (Spec.map (CommRingCat.ofHom π))) :=
    inferInstance
  have h3 : LocallyOfFiniteType (pullback.snd (Spec.map ψ) (Spec.map (CommRingCat.ofHom π))) := by
    rwa [hψ, ← pullbackRightPullbackFstIso_inv_snd_snd,
      MorphismProperty.cancel_left_of_respectsIso (P := @LocallyOfFiniteType)]
  have key := locallyOfFiniteType_specMap_of_pullback_snd π hπs hπn ψ h3
  rwa [hψ] at key
private lemma isSeparated_of_isSeparated_comp_of_surjective
  {X X' S : (Scheme : Type 1)}
  (k : X' ⟶ X)
  (f : X ⟶ S)
  [IsClosedImmersion k] [Surjective k] [IsSeparated (k ≫ f)] :
  -- imply
  IsSeparated f := by
  -- proof
  let μ := pullback.map (k ≫ f) (k ≫ f) f f k k (𝟙 S) ((Category.comp_id _).trans rfl) ((Category.comp_id _).trans rfl)
  have hμc : IsClosedImmersion μ := MorphismProperty.pullbackMap (P := @IsClosedImmersion) ‹_› ‹_› rfl rfl
  have hcomm : k ≫ pullback.diagonal f = pullback.diagonal (k ≫ f) ≫ μ := by
    apply pullback.hom_ext
    · simp only [μ, pullback.diagonal, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id, Category.id_comp]
    · simp only [μ, pullback.diagonal, pullback.map, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]
  have hrange : Set.range (pullback.diagonal f).base = μ.base '' Set.range (pullback.diagonal (k ≫ f)).base := by
    have h1 : Set.range (pullback.diagonal f).base = Set.range (k ≫ pullback.diagonal f).base := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr (Surjective.surj (f := k)), Set.image_univ]
    rw [h1, hcomm, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  refine ⟨IsClosedImmersion.of_isPreimmersion _ ?_⟩
  rw [hrange]
  apply hμc.isClosedEmbedding.isClosedMap _ (pullback.diagonal (k ≫ f)).isClosedEmbedding.isClosed_range
private lemma gamma2
  {P B' : Type} [CommRing P] [CommRing B']
  (π : P →+* B')
  (hπs : Function.Surjective π)
  {X X' : (Scheme : Type 1)}
  (f : X ⟶ Spec (CommRingCat.of P))
  (f' : X' ⟶ Spec (CommRingCat.of B'))
  (k' : X' ⟶ X)
  (hk : IsPullback k' f' f (Spec.map (CommRingCat.ofHom π)))
  [IsClosedImmersion k'] [Surjective k'] [LocallyOfFiniteType f]
  (hp : IsProper f') :
  -- imply
  IsProper f := by
  -- proof
  let _ : IsClosedImmersion (Spec.map (CommRingCat.ofHom π)) := IsClosedImmersion.spec_of_surjective _ hπs
  let _ : IsProper (k' ≫ f) := by
    rw [hk.w]
    infer_instance
  let _ : UniversallyClosed f := UniversallyClosed.of_comp_surjective k' f
  let _ : IsSeparated f := isSeparated_of_isSeparated_comp_of_surjective k' f
  constructor
private lemma isIso_residueFieldMap_of_surjectiveOnStalks
  {X Y : (Scheme : Type 1)}
  (g : X ⟶ Y) [SurjectiveOnStalks g]
  (x : X) :
  -- imply
  IsIso (g.residueFieldMap x) := by
  -- proof
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(g.residueFieldMap x).hom.injective, ?_⟩
  have hs : Function.Surjective ((g.stalkMap x ≫ X.residue x).hom) := by
    rw [CommRingCat.hom_comp, RingHom.coe_comp]
    apply (X.residue_surjective x).comp (g.stalkMap_surjective x)
  rw [← Scheme.residue_residueFieldMap, CommRingCat.hom_comp, RingHom.coe_comp] at hs
  apply Function.Surjective.of_comp hs
private lemma smooth_of_isPullback_of_isIso
  {A B C D : (Scheme : Type 1)}
  {fst : A ⟶ B} {snd : A ⟶ C} {u : B ⟶ D} {v : C ⟶ D}
  -- given
  (sq : IsPullback fst snd u v)
  (hv : IsIso v)
  (hs : Smooth snd) :
  -- imply
  Smooth u := by
  -- proof
  let _ : IsIso (pullback.fst u v) := inferInstance
  let _ : IsIso fst := by
    rw [← sq.isoPullback_hom_fst]
    infer_instance
  have hu : u = inv fst ≫ snd ≫ v := by
    rw [← sq.w, IsIso.inv_hom_id_assoc]
  rw [hu]
  infer_instance
private lemma gamma3
  {P B' : Type} [CommRing P] [CommRing B']
  (π : P →+* B')
  (hπs : Function.Surjective π)
  {X X' : (Scheme : Type 1)}
  (f : X ⟶ Spec (CommRingCat.of P))
  (f' : X' ⟶ Spec (CommRingCat.of B'))
  (k' : X' ⟶ X)
  (hk : IsPullback k' f' f (Spec.map (CommRingCat.ofHom π)))
  (hsurj : Surjective (Spec.map (CommRingCat.ofHom π)))
  (hfl : Flat f)
  (hfp : LocallyOfFinitePresentation f)
  (hsm : Smooth f') :
  -- imply
  Smooth f := by
  -- proof
  let _ : IsClosedImmersion (Spec.map (CommRingCat.ofHom π)) := IsClosedImmersion.spec_of_surjective _ hπs
  refine Smooth.of_smooth_fiberToSpecResidueField f fun y => ?_
  obtain ⟨y', rfl⟩ := hsurj.1 y
  have sq := isPullback_fiberToSpecResidueField_of_isPullback hk y'
  let _ : IsIso ((Spec.map (CommRingCat.ofHom π)).residueFieldMap y') :=
    isIso_residueFieldMap_of_surjectiveOnStalks _ y'
  apply smooth_of_isPullback_of_isIso sq inferInstance
  apply MorphismProperty.pullback_snd (P := @Smooth) _ _ hsm
/--
[AlgebraicGeometry_isClosedImmersion_and_isProper_and_smooth_of_isPullback_specMap_of_surjective_of_isNilpotent_ker](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isClosedImmersion_and_isProper_and_smooth_of_isPullback_specMap_of_surjective_of_isNilpotent_ker.lean)
-/
@[path]
private lemma main
  {P B' : Type} [CommRing P] [CommRing B']
  (π : P →+* B')
  (hπs : Function.Surjective π)
  (hπn : IsNilpotent (RingHom.ker π))
  {X X' : (Scheme : Type 1)}
  (f : X ⟶ Spec (CommRingCat.of P))
  (f' : X' ⟶ Spec (CommRingCat.of B'))
  (k' : X' ⟶ X)
  (hk : IsPullback k' f' f (Spec.map (CommRingCat.ofHom π))) :
  -- imply
  (IsClosedImmersion k' ∧ Function.Bijective k'.base) ∧
    (LocallyOfFiniteType f' → LocallyOfFiniteType f) ∧
    (IsProper f' → IsProper f) ∧
    (Flat f → LocallyOfFinitePresentation f → Smooth f' → Smooth f) := by
  -- proof
  obtain ⟨hci, hbij⟩ := gamma0 π hπs hπn f f' k' hk
  have hsurj : Surjective (Spec.map (CommRingCat.ofHom π)) :=
    surjective_specMap_of_surjective_of_isNilpotent_ker π hπs hπn
  refine ⟨⟨hci, hbij⟩, fun h => gamma1 π hπs hπn f f' k' hk h, fun hp => ?_, fun hfl hfp hsm => ?_⟩
  ·
    let _ : IsClosedImmersion k' := hci
    let _ : Surjective k' := ⟨hbij.2⟩
    let _ : LocallyOfFiniteType f := gamma1 π hπs hπn f f' k' hk inferInstance
    apply gamma2 π hπs f f' k' hk hp
  · apply gamma3 π hπs f f' k' hk hsurj hfl hfp hsm


-- created on 2026-10-20
