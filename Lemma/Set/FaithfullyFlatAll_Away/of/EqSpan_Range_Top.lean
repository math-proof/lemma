import Mathlib
import sympy.Basic


/--
[Module_faithfullyFlat_pi_localizationAway_of_span_eq_top](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_faithfullyFlat_pi_localizationAway_of_span_eq_top.lean)
-/
@[main]
private lemma main
  {S : Type u} [CommRing S]
  {k : ℕ}
  {r : Fin k → S}
-- given
  (hr : Ideal.span (Set.range r) = ⊤) :
-- imply
  Module.FaithfullyFlat S (∀ i : Fin k, Localization.Away (r i)) := by
-- proof
  classical

  have : Module.Flat S (∀ i : Fin k, Localization.Away (r i)) :=
    Module.Flat.of_linearEquiv (DirectSum.linearEquivFunOnFintype S (Fin k) (fun i => Localization.Away (r i))).symm
  refine Module.FaithfullyFlat.of_comap_surjective fun p => ?_

  have hi : ∃ i, r i ∉ p.asIdeal := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have : Ideal.span (Set.range r) ≤ p.asIdeal := Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hcon i)
    rw [hr, top_le_iff] at this
    exact p.2.ne_top this
  obtain ⟨i, hi⟩ := hi

  have hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away (r i)))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away (r i)) (r i)]
    exact hi
  obtain ⟨q, hq⟩ := hp
  refine ⟨PrimeSpectrum.comap (Pi.evalRingHom (fun j : Fin k => Localization.Away (r j)) i) q, ?_⟩
  rw [← PrimeSpectrum.comap_comp_apply]
  have : (Pi.evalRingHom (fun j : Fin k => Localization.Away (r j)) i).comp
      (algebraMap S (∀ j : Fin k, Localization.Away (r j))) = algebraMap S (Localization.Away (r i)) :=
    RingHom.ext fun _ => rfl
  rw [this, hq]


-- created on 2026-10-05
