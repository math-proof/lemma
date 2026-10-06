import Mathlib
import sympy.Basic


/--
[IsLocalization_exists_not_mem_forall_algebraMap_away_eq_zero_of_algebraMap_atPrime_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalization_exists_not_mem_forall_algebraMap_away_eq_zero_of_algebraMap_atPrime_eq_zero.lean)
-/
@[main]
private lemma main
  {S : Type u} [CommRing S] [IsNoetherianRing S]
  {𝔭 : PrimeSpectrum S} :
-- imply
  ∃ g : S, g ∉ 𝔭.asIdeal ∧ ∀ x : S, algebraMap S (Localization.AtPrime 𝔭.asIdeal) x = 0 →
      algebraMap S (Localization.Away g) x = 0 := by
-- proof
  classical
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian (RingHom.ker (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))
  have hmem : ∀ x ∈ s, ∃ m : S, m ∉ 𝔭.asIdeal ∧ m * x = 0 := by
    intro x hx
    have hxK : x ∈ RingHom.ker (algebraMap S (Localization.AtPrime 𝔭.asIdeal)) := hs ▸ Submodule.subset_span hx
    rw [RingHom.mem_ker, IsLocalization.map_eq_zero_iff 𝔭.asIdeal.primeCompl] at hxK
    obtain ⟨m, hm⟩ := hxK
    exact ⟨m, m.2, hm⟩
  choose m hm₁ hm₂ using hmem
  have hgK : ∀ y ∈ RingHom.ker (algebraMap S (Localization.AtPrime 𝔭.asIdeal)), (∏ x ∈ s.attach, m x.1 x.2) * y = 0 := by
    intro y hy
    rw [← hs] at hy
    induction hy using Submodule.span_induction with
    | mem y hys =>
      obtain ⟨c, hc⟩ : m y hys ∣ ∏ x ∈ s.attach, m x.1 x.2 :=
        Finset.dvd_prod_of_mem (fun x : {x // x ∈ s} => m x.1 x.2) (Finset.mem_attach s ⟨y, hys⟩)
      rw [hc, mul_right_comm, hm₂ y hys, zero_mul]
    | zero => rw [mul_zero]
    | add a b _ _ ha hb => rw [mul_add, ha, hb, add_zero]
    | smul a b _ hb => rw [smul_eq_mul, mul_left_comm, hb, mul_zero]
  refine ⟨∏ x ∈ s.attach, m x.1 x.2, ?_, ?_⟩
  · have hg : (∏ x ∈ s.attach, m x.1 x.2) ∈ 𝔭.asIdeal.primeCompl :=
      Submonoid.prod_mem _ (fun x _ => (hm₁ x.1 x.2 : m x.1 x.2 ∈ 𝔭.asIdeal.primeCompl))
    exact hg
  · intro x hx
    rw [IsLocalization.map_eq_zero_iff (Submonoid.powers (∏ x ∈ s.attach, m x.1 x.2))]
    exact ⟨⟨_, Submonoid.mem_powers _⟩, hgK x hx⟩


-- created on 2026-10-05
