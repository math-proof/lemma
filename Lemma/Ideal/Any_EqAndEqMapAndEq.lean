import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma exists_not_mem
  {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
  (x : PrimeSpectrum S) : ∃ i, r i ∉ x.asIdeal := by
  by_contra h
  push Not at h
  have hle : Ideal.span (Set.range r) ≤ x.asIdeal := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    apply h i
  rw [hr, top_le_iff] at hle
  apply x.isPrime.ne_top hle
private lemma cov_covers
  {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
  (B : Fin k → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)] [∀ i, IsLocalization.Away (r i) (B i)]
  (x : Spec (CommRingCat.of S)) :
  ∃ i y, (Spec.map (CommRingCat.ofHom (algebraMap S (B i)))).base y = x := by
  obtain ⟨i, hi⟩ := exists_not_mem r hr x
  have hx : x ∈ Set.range (PrimeSpectrum.comap (algebraMap S (B i))) := by
    rwa [PrimeSpectrum.localization_away_comap_range (B i) (r i)]
  obtain ⟨y, hy⟩ := hx
  exact ⟨i, y, hy⟩
private noncomputable def cov
  {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
  (B : Fin k → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)] [∀ i, IsLocalization.Away (r i) (B i)] :
  (Spec (CommRingCat.of S)).OpenCover :=
  Scheme.Cover.mkOfCovers (Fin k) (fun i => Spec (CommRingCat.of (B i)))
    (fun i => Spec.map (CommRingCat.ofHom (algebraMap S (B i))))
    (cov_covers r hr B)
    (fun i => IsOpenImmersion.of_isLocalization (r i))
/--
[AlgebraicGeometry_Scheme_existsUnique_section_of_forall_away](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_existsUnique_section_of_forall_away.lean)
-/
@[path]
private lemma main
  {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
  (B : Fin k → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)] [∀ i, IsLocalization.Away (r i) (B i)]
  {A : (Scheme : Type (u + 1))} (f : A ⟶ Spec (CommRingCat.of S))
  (σ : ∀ i, Spec (CommRingCat.of (B i)) ⟶ A)
  (hσ : ∀ i, σ i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap S (B i))))
  (hagree : ∀ (i j : Fin k) (C : Type u) [CommRing C] [Algebra S C] [IsLocalization.Away (r i * r j) C] (ρ₁ : AlgHom S (B i) C) (ρ₂ : AlgHom S (B j) C), Spec.map (CommRingCat.ofHom ρ₁.toRingHom) ≫ σ i = Spec.map (CommRingCat.ofHom ρ₂.toRingHom) ≫ σ j) :
  ∃ σ₀ : Spec (CommRingCat.of S) ⟶ A, σ₀ ≫ f = 𝟙 _ ∧
    (∀ i, Spec.map (CommRingCat.ofHom (algebraMap S (B i))) ≫ σ₀ = σ i) ∧
    ∀ σ₁ : Spec (CommRingCat.of S) ⟶ A, (∀ i, Spec.map (CommRingCat.ofHom (algebraMap S (B i))) ≫ σ₁ = σ i) → σ₁ = σ₀ := by
  let 𝒰 := cov r hr B
  have hcompat : ∀ i j : Fin k, pullback.fst (𝒰.f i) (𝒰.f j) ≫ σ i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ σ j := by
    intro i j
    let _ : IsLocalization.Away (r i * r j) (TensorProduct S (B i) (B j)) :=
      IsLocalization.Away.mul' (B i) (TensorProduct S (B i) (B j)) (r i) (r j)
    have h := hagree i j (TensorProduct S (B i) (B j)) Algebra.TensorProduct.includeLeft Algebra.TensorProduct.includeRight
    change pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap S (B i)))) (Spec.map (CommRingCat.ofHom (algebraMap S (B j)))) ≫ σ i =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S (B i)))) (Spec.map (CommRingCat.ofHom (algebraMap S (B j)))) ≫ σ j
    rw [← cancel_epi (pullbackSpecIso S (B i) (B j)).inv]
    show (pullbackSpecIso S (B i) (B j)).inv ≫ pullback.fst _ _ ≫ σ i = (pullbackSpecIso S (B i) (B j)).inv ≫ pullback.snd _ _ ≫ σ j
    rwa [pullbackSpecIso_inv_fst_assoc, pullbackSpecIso_inv_snd_assoc]
  refine ⟨𝒰.glueMorphisms σ hcompat, ?_, fun i => 𝒰.ι_glueMorphisms σ hcompat i, ?_⟩
  ·
    refine 𝒰.hom_ext _ _ fun i => ?_
    rw [𝒰.ι_glueMorphisms_assoc, Category.comp_id]
    apply hσ i
  ·
    intro σ₁ hσ₁
    refine 𝒰.hom_ext _ _ fun i => ?_
    rw [𝒰.ι_glueMorphisms]
    apply hσ₁ i


-- created on 2026-10-20
