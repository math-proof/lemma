import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma locallyQuasiFinite_of_etale
  {κ : Type u} [Field κ] {E : (Scheme : Type (u + 1))} (fE : E ⟶ Spec (CommRingCat.of κ)) [Etale fE] :
    LocallyQuasiFinite fE := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyQuasiFinite)]
  intro U V e
  have hEt : RingHom.Etale (fE.appLE U V e).hom := HasRingHomProperty.appLE (P := @Etale) fE inferInstance U V e
  algebraize [(fE.appLE U V e).hom]
  have : Algebra.Etale ((Spec (CommRingCat.of κ)).presheaf.obj (op U)) (E.presheaf.obj (op V)) := hEt
  change Algebra.QuasiFinite _ _
  infer_instance
private lemma exists_openImmersion_specPoint
  {κ : Type u} [Field κ] [IsAlgClosed κ] {E : (Scheme : Type (u + 1))} (fE : E ⟶ Spec (CommRingCat.of κ)) [Etale fE] (e : E) :
    ∃ (y : Spec (CommRingCat.of κ) ⟶ E), IsOpenImmersion y ∧ y ≫ fE = 𝟙 _ ∧ e ∈ Set.range y.base := by
  classical
  let _ := locallyQuasiFinite_of_etale fE
  have hdisc : _root_.IsDiscrete (Set.univ : Set E) := by
    apply (congrArg _root_.IsDiscrete (Set.eq_univ_of_forall fun x => Subsingleton.elim _ _)).mp
      (fE.isDiscrete_preimage_singleton (IsLocalRing.closedPoint κ))
  let _ : DiscreteTopology E := isDiscrete_univ_iff.1 hdisc
  have hopen : IsOpen ({e} : Set E) := isOpen_discrete _
  obtain ⟨R, ι, hι, he, hsub⟩ := AlgebraicGeometry.Scheme.exists_affine_mem_range_and_range_subset
    (U := ⟨{e}, hopen⟩) (x := e) rfl
  let _ : IsOpenImmersion ι := hι
  have hrange : Set.range ι.base = {e} := Set.Subset.antisymm hsub (Set.singleton_subset_iff.2 he)
  have hsub1 : Subsingleton (Spec (CommRingCat.of R)) := by
    refine ⟨fun a b => ι.isOpenEmbedding.injective ?_⟩
    have ha : ι.base a ∈ ({e} : Set E) := hrange ▸ ⟨a, rfl⟩
    have hb : ι.base b ∈ ({e} : Set E) := hrange ▸ ⟨b, rfl⟩
    rw [Set.mem_singleton_iff] at ha hb
    rw [ha, hb]
  obtain ⟨a₀, ha₀⟩ := he
  let _ : IsLocalRing R := by
    refine IsLocalRing.of_unique_max_ideal ⟨(a₀ : PrimeSpectrum R).asIdeal, ?_, ?_⟩
    ·
      obtain ⟨M, hM, _⟩ := Ideal.exists_le_maximal _ (a₀ : PrimeSpectrum R).isPrime.ne_top
      have : (⟨M, hM.isPrime⟩ : PrimeSpectrum R) = a₀ := Subsingleton.elim (α := Spec (CommRingCat.of R)) _ _
      rwa [← this]
    ·
      intro I hI
      have : (⟨I, hI.isPrime⟩ : PrimeSpectrum R) = a₀ := Subsingleton.elim (α := Spec (CommRingCat.of R)) _ _
      apply congrArg PrimeSpectrum.asIdeal this
  set ρ : CommRingCat.of κ ⟶ CommRingCat.of R := Spec.preimage (ι ≫ fE)
  have hρ : Spec.map ρ = ι ≫ fE := Spec.map_preimage _
  have hρet : RingHom.Etale ρ.hom := by
    have : Etale (Spec.map ρ) := by
      rw [hρ]
      infer_instance
    apply HasRingHomProperty.Spec_iff.mp this
  algebraize [ρ.hom]
  have : Algebra.Etale κ R := hρet
  have hbij : Function.Bijective (algebraMap κ R) :=
    Algebra.FormallyUnramified.bijective_of_isAlgClosed_of_isLocalRing κ R
  let eρ : RingEquiv κ R := RingEquiv.ofBijective (algebraMap κ R) hbij
  let σ : CommRingCat.of R ⟶ CommRingCat.of κ := CommRingCat.ofHom eρ.symm.toRingHom
  have hρσ : ρ ≫ σ = 𝟙 _ := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change eρ.symm (algebraMap κ R a) = a
    apply eρ.symm_apply_apply a
  let _ : IsIso σ := by
    refine ⟨⟨ρ, ?_, hρσ⟩⟩
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    change algebraMap κ R (eρ.symm b) = b
    apply eρ.apply_symm_apply b
  refine ⟨Spec.map σ ≫ ι, inferInstance, ?_, ?_⟩
  · rw [Category.assoc, ← hρ, ← Spec.map_comp, hρσ, Spec.map_id]
  ·
    refine ⟨(inv (Spec.map σ)).base a₀, ?_⟩
    change ((inv (Spec.map σ)) ≫ (Spec.map σ ≫ ι)).base a₀ = e
    rwa [IsIso.inv_hom_id_assoc]
/--
[AlgebraicGeometry_isReduced_pullback_of_etale_of_forall_isReduced_pullback](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isReduced_pullback_of_etale_of_forall_isReduced_pullback.lean)
-/
@[path]
private lemma main
  {κ : Type u} [Field κ] [IsAlgClosed κ] {X Y E : (Scheme : Type (u + 1))}
  (f : X ⟶ Y) (g : E ⟶ Y) (fE : E ⟶ Spec (CommRingCat.of κ)) [Etale fE]
  (h : ∀ y : Spec (CommRingCat.of κ) ⟶ E, y ≫ fE = 𝟙 _ → IsReduced (pullback f (y ≫ g))) :
    IsReduced (pullback f g) := by
  classical
  choose y hyo hyf hye using exists_openImmersion_specPoint fE
  let 𝒰 : E.OpenCover := Scheme.Cover.mkOfCovers E (fun _ => Spec (CommRingCat.of κ)) y
    (fun x => (hye x).elim fun a ha => ⟨x, a, ha⟩) (fun e => hyo e)
  let _ : ∀ i, IsReduced ((Scheme.Pullback.openCoverOfRight 𝒰 f g).X i) := fun i => h (y i) (hyf i)
  apply IsReduced.of_openCover (X := pullback f g) (Scheme.Pullback.openCoverOfRight 𝒰 f g)


-- created on 2026-10-20
