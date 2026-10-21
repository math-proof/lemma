import Mathlib
import sympy.Basic
open IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[IsIntegrallyClosed_isRegularLocalRing_localization_of_ne_maximalIdeal_of_ringKrullDim_le_two](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsIntegrallyClosed_isRegularLocalRing_localization_of_ne_maximalIdeal_of_ringKrullDim_le_two.lean)
-/
@[path]
private lemma main
  [CommRing R₀] [IsDomain R₀] [IsNoetherianRing R₀] [IsLocalRing R₀] [IsIntegrallyClosed R₀]
  (𝔯 : Ideal R₀) [𝔯.IsPrime]
  -- given
  (hdim : ringKrullDim R₀ ≤ (2 : WithBot ENat))
  (h𝔯 : 𝔯 ≠ maximalIdeal R₀) :
  -- imply
  IsRegularLocalRing (Localization.AtPrime 𝔯) := by
  -- proof
  classical
  set A := Localization.AtPrime 𝔯
  have hlt : 𝔯 < maximalIdeal R₀ :=
    lt_of_le_of_ne (le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) h𝔯
  have h1 : 𝔯.height + 1 ≤ (maximalIdeal R₀).height :=
    Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have hm : (maximalIdeal R₀).height ≤ 2 := by
    have h2 := maximalIdeal_height_eq_ringKrullDim (R := R₀)
    rw [← h2] at hdim
    apply WithBot.coe_le_coe.mp hdim
  have hrh : 𝔯.height ≤ 1 := by
    have h3 : 𝔯.height + 1 ≤ 2 := h1.trans hm
    have hne : 𝔯.height ≠ ⊤ := by
      intro htop
      rw [htop] at h3
      apply absurd h3 (by decide)
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
    rw [← hn] at h3 ⊢
    have : (n : ENat) + 1 = ((n + 1 : ℕ) : ENat) := by
      push_cast
      rfl
    rw [this] at h3
    have h4 : n + 1 ≤ 2 := by
      exact_mod_cast h3
    exact_mod_cast (by omega : n ≤ 1)
  have hdimA : ringKrullDim A ≤ 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔯 A]
    exact_mod_cast hrh
  let hic : IsIntegrallyClosed A :=
    isIntegrallyClosed_of_isLocalization A 𝔯.primeCompl (Ideal.primeCompl_le_nonZeroDivisors 𝔯)
  if hF : IsField A then
    let _ : Field A := hF.toField
    infer_instance
  else
    let _ : Ring.DimensionLEOne A := by
      refine ⟨fun {p} hp0 hp => ?_⟩
      let _ : p.IsPrime := hp
      have hb : (⊥ : Ideal A) < p := bot_lt_iff_ne_bot.mpr hp0
      have hh : (⊥ : Ideal A).height + 1 ≤ p.height := Ideal.height_add_one_le_of_lt_of_isPrime hb
      rw [Ideal.height_bot, zero_add] at hh
      have hle : (p.height : WithBot ENat) ≤ ringKrullDim A := Ideal.height_le_ringKrullDim_of_isPrime
      refine Ideal.isMaximal_of_height_eq_ringKrullDim (le_antisymm hle (hdimA.trans (by exact_mod_cast hh)))
    let _ : IsNoetherianRing A := IsLocalization.isNoetherianRing 𝔯.primeCompl A inferInstance
    have hded : IsDedekindDomain A := { }
    let _ : IsDiscreteValuationRing A := ((IsDiscreteValuationRing.TFAE A hF).out 1 3).mpr hded
    infer_instance


-- created on 2026-10-20
