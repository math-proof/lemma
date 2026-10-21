import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false


universe u

/--
[AlgebraicGeometry_existsUnique_specMap_algebraMap_away_comp_eq_of_sum_eq_one_of_orthogonal](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_existsUnique_specMap_algebraMap_away_comp_eq_of_sum_eq_one_of_orthogonal.lean)
-/
@[path]
private lemma main
  {S : Type u} [CommRing S] {m : ℕ} (ε : Fin m → S)
  (hε : ∀ k, IsIdempotentElem (ε k)) (hsum : ∑ k, ε k = 1) (horth : ∀ k l, k ≠ l → ε k * ε l = 0)
  {A : (Scheme : Type (u + 1))} (x : ∀ k, Spec (CommRingCat.of (Localization.Away (ε k))) ⟶ A) :
  -- imply
  ∃! y : Spec (CommRingCat.of S) ⟶ A, ∀ k, Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (ε k)))) ≫ y = x k := by
  -- proof
  classical
  have hs : Ideal.span (Set.range ε) = ⊤ := by
    rw [Ideal.eq_top_iff_one, ← hsum]
    apply Ideal.sum_mem _ fun k _ => Ideal.subset_span (Set.mem_range_self k)
  let 𝒰 : (Spec (CommRingCat.of S)).OpenCover := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of S) ε hs).openCover
  have h𝒰f : ∀ k : Fin m, 𝒰.f k = Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (ε k)))) := fun _ => rfl
  have hrange : ∀ (k : Fin m) (p : Spec (CommRingCat.of (Localization.Away (ε k)))), ε k ∉ ((Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (ε k))))).base p).asIdeal := by
    intro k p
    have hmem : (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (ε k))))).base p ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away (ε k)))) := ⟨p, rfl⟩
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away (ε k)) (ε k)] at hmem
    apply hmem
  have hempty : ∀ k l : Fin m, k ≠ l → IsEmpty (CategoryTheory.Limits.pullback (C := (Scheme : Type (u + 1))) (𝒰.f k) (𝒰.f l)) := by
    intro k l hkl
    refine ⟨fun p => ?_⟩
    let q := (CategoryTheory.Limits.pullback.fst (𝒰.f k) (𝒰.f l) ≫ 𝒰.f k).base p
    have hk : ε k ∉ q.asIdeal := by
      show ε k ∉ ((𝒰.f k).base ((CategoryTheory.Limits.pullback.fst (𝒰.f k) (𝒰.f l)).base p)).asIdeal
      apply hrange k _
    have hl : ε l ∉ q.asIdeal := by
      have : q = (CategoryTheory.Limits.pullback.snd (𝒰.f k) (𝒰.f l) ≫ 𝒰.f l).base p := by
        show (CategoryTheory.Limits.pullback.fst (𝒰.f k) (𝒰.f l) ≫ 𝒰.f k).base p = _
        rw [CategoryTheory.Limits.pullback.condition]
      rw [this]
      show ε l ∉ ((𝒰.f l).base ((CategoryTheory.Limits.pullback.snd (𝒰.f k) (𝒰.f l)).base p)).asIdeal
      apply hrange l _
    have h0 : ε k * ε l ∈ q.asIdeal := by
      rw [horth k l hkl]
      apply q.asIdeal.zero_mem
    refine (q.isPrime.mem_or_mem h0).elim hk hl
  have hf : ∀ k l : Fin m, CategoryTheory.Limits.pullback.fst (𝒰.f k) (𝒰.f l) ≫ x k = CategoryTheory.Limits.pullback.snd _ _ ≫ x l := by
    intro k l
    if hkl : k = l then
      subst hkl
      apply congrArg (fun t => t ≫ x k) (fst_eq_snd_of_mono_eq (𝒰.f k))
    else
      let _ := hempty k l hkl
      apply Limits.IsInitial.hom_ext isInitialOfIsEmpty _ _
  refine ⟨Scheme.Cover.glueMorphisms 𝒰 x hf, fun k => Scheme.Cover.ι_glueMorphisms 𝒰 x hf k, ?_⟩
  intro y hy
  apply Scheme.Cover.hom_ext 𝒰 _ _ fun k => by
    rw [Scheme.Cover.ι_glueMorphisms]
    apply hy k


-- created on 2026-10-20
