import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[AlgebraicGeometry_existsUnique_specMap_algebraMap_away_comp_eq_of_sum_eq_one_of_orthogonal](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_existsUnique_specMap_algebraMap_away_comp_eq_of_sum_eq_one_of_orthogonal.lean)
-/
@[path]
private lemma main
    {S : Type u} [CommRing S] {m : ℕ} (ε : Fin m → S)
    (hε : ∀ k, IsIdempotentElem (ε k)) (hsum : ∑ k, ε k = 1) (horth : ∀ k l, k ≠ l → ε k * ε l = 0)
    {A : Scheme.{u}} (x : ∀ k, Spec (CommRingCat.of (Localization.Away (ε k))) ⟶ A) :
    ∃! y : Spec (CommRingCat.of S) ⟶ A,
      ∀ k, Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (ε k)))) ≫ y = x k := by
  classical
  have hs : Ideal.span (Set.range ε) = ⊤ := by
    rw [Ideal.eq_top_iff_one, ← hsum]
    exact Ideal.sum_mem _ fun k _ => Ideal.subset_span ⟨k, rfl⟩
  let 𝒰 : (Spec (CommRingCat.of S)).OpenCover :=
    (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of S) ε hs).openCover
  have h𝒰f : ∀ k : Fin m, 𝒰.f k = Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (ε k)))) := fun _ => rfl
  have hrange : ∀ (k : Fin m) (p : ↥(Spec (CommRingCat.of (Localization.Away (ε k))))),
      ε k ∉ ((Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (ε k))))).base p).asIdeal := by
    intro k p
    have hmem : (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (ε k))))).base p ∈
        Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away (ε k)))) := ⟨p, rfl⟩
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away (ε k)) (ε k)] at hmem
    exact hmem
  have hempty : ∀ k l : Fin m, k ≠ l → IsEmpty ↥(pullback (𝒰.f k) (𝒰.f l)) := by
    intro k l hkl
    refine ⟨fun p => ?_⟩
    let q := (pullback.fst (𝒰.f k) (𝒰.f l) ≫ 𝒰.f k).base p
    have hk : ε k ∉ q.asIdeal := by
      show ε k ∉ ((𝒰.f k).base ((pullback.fst (𝒰.f k) (𝒰.f l)).base p)).asIdeal
      exact hrange k _
    have hl : ε l ∉ q.asIdeal := by
      have : q = (pullback.snd (𝒰.f k) (𝒰.f l) ≫ 𝒰.f l).base p := by
        show (pullback.fst (𝒰.f k) (𝒰.f l) ≫ 𝒰.f k).base p = _
        rw [pullback.condition]
      rw [this]
      show ε l ∉ ((𝒰.f l).base ((pullback.snd (𝒰.f k) (𝒰.f l)).base p)).asIdeal
      exact hrange l _
    have h0 : ε k * ε l ∈ q.asIdeal := by rw [horth k l hkl]; exact q.asIdeal.zero_mem
    exact (q.isPrime.mem_or_mem h0).elim hk hl
  have hf : ∀ k l : Fin m, pullback.fst (𝒰.f k) (𝒰.f l) ≫ x k = pullback.snd _ _ ≫ x l := by
    intro k l
    by_cases hkl : k = l
    · subst hkl
      exact congrArg (fun t => t ≫ x k) (fst_eq_snd_of_mono_eq (𝒰.f k))
    · haveI := hempty k l hkl
      exact Limits.IsInitial.hom_ext isInitialOfIsEmpty _ _
  refine ⟨Scheme.Cover.glueMorphisms 𝒰 x hf, fun k => Scheme.Cover.ι_glueMorphisms 𝒰 x hf k, ?_⟩
  intro y hy
  exact Scheme.Cover.hom_ext 𝒰 _ _ fun k => by
    rw [Scheme.Cover.ι_glueMorphisms]
    exact hy k

-- created on 2026-10-20
