import Mathlib
import sympy.Basic


/--
[CerednikDrinfeld_exists_ringHom_away_comp_eq_and_not_mem_iff](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CerednikDrinfeld_exists_ringHom_away_comp_eq_and_not_mem_iff.lean)
-/
@[main]
private lemma main
  {B B' : Type} [CommRing B] [CommRing B']
  {f : B →+* B'}
  {g : B} :
-- imply
  (∃ fg : Localization.Away g →+* Localization.Away (f g),
        fg.comp (algebraMap B (Localization.Away g)) = (algebraMap B' (Localization.Away (f g))).comp f) ∧
      ∀ x' : PrimeSpectrum B', f g ∉ x'.asIdeal ↔ g ∉ (PrimeSpectrum.comap f x').asIdeal := by
-- proof
  have hle : Submonoid.powers g ≤ (Submonoid.powers (f g)).comap f := by
    rintro x ⟨n, rfl⟩
    exact ⟨n, by simp [map_pow]⟩
  refine ⟨⟨IsLocalization.map (Localization.Away (f g)) f hle, IsLocalization.map_comp hle⟩, fun x' => ?_⟩
  simp [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]


-- created on 2026-10-03
