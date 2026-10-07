import Mathlib
import sympy.Basic

open scoped TensorProduct

/--
[Algebra_Etale_finite_etale_faithfullyFlat_away_of_isIdempotentElem](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_Etale_finite_etale_faithfullyFlat_away_of_isIdempotentElem.lean)
-/
@[main]
private lemma main
  {S C : Type} [CommRing S] [CommRing C] [Algebra S C] [Module.Finite S C] [Algebra.Etale S C]
  {e : C}
-- given
  (he : IsIdempotentElem e)
  (hsurj : ∀ 𝔮 : Ideal S, 𝔮.IsPrime → ∃ 𝔭 : Ideal C, 𝔭.IsPrime ∧ 𝔭.comap (algebraMap S C) = 𝔮 ∧ e ∉ 𝔭) :
-- imply
  Module.Finite S (Localization.Away e) ∧ Algebra.Etale S (Localization.Away e) ∧
      Module.FaithfullyFlat S (Localization.Away e) := by
-- proof
  classical

  have hs : Function.Surjective (algebraMap C (Localization.Away e)) :=
    IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem e he
  have hfin : Module.Finite S (Localization.Away e) :=
    Module.Finite.of_surjective (IsScalarTower.toAlgHom S C (Localization.Away e)).toLinearMap hs

  have het : Algebra.Etale S (Localization.Away e) := inferInstance

  have hff : Module.FaithfullyFlat S (Localization.Away e) := by
    refine Module.FaithfullyFlat.of_comap_surjective ?_
    intro 𝔮
    obtain ⟨𝔭, h𝔭, h𝔭𝔮, he𝔭⟩ := hsurj 𝔮.asIdeal 𝔮.isPrime
    have hd : Disjoint ((Submonoid.powers e : Submonoid C) : Set C) (𝔭 : Set C) := by
      rw [Set.disjoint_left]
      rintro x ⟨n, rfl⟩ hx
      rcases n with _ | n
      · exact h𝔭.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using hx))
      · exact he𝔭 (h𝔭.mem_of_pow_mem (n + 1) hx)
    have h𝔓 : (Ideal.map (algebraMap C (Localization.Away e)) 𝔭).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers e) (Localization.Away e) 𝔭 h𝔭 hd
    refine ⟨⟨Ideal.map (algebraMap C (Localization.Away e)) 𝔭, h𝔓⟩, ?_⟩
    apply PrimeSpectrum.ext
    change (Ideal.map (algebraMap C (Localization.Away e)) 𝔭).comap (algebraMap S (Localization.Away e)) = 𝔮.asIdeal
    rw [IsScalarTower.algebraMap_eq S C (Localization.Away e), ← Ideal.comap_comap,
      ← Ideal.under_def C, IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers e) (Localization.Away e) h𝔭 hd, h𝔭𝔮]
  exact ⟨hfin, het, hff⟩


-- created on 2026-10-05
