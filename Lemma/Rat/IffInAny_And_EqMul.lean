import Mathlib
import Initialize.Tactic.Attr.Basic
open IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[ValuationSubring_mem_iff_exists_not_dvd_of_prime_of_forall_mem_maximalIdeal_iff_dvd](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ValuationSubring_mem_iff_exists_not_dvd_of_prime_of_forall_mem_maximalIdeal_iff_dvd.lean)
-/
@[path]
private lemma main
  [Field K] (S : Subring K) [IsNoetherianRing ↥S] (ϖ : ↥S) (hϖ : Prime ϖ)
  (O : ValuationSubring K) (hSO : ∀ s : ↥S, (s : K) ∈ O)
  (hcen : ∀ s : ↥S, (⟨(s : K), hSO s⟩ : ↥O) ∈ maximalIdeal ↥O ↔ ϖ ∣ s) :
  -- imply
  ∀ f : K, (∃ g h : ↥S, (h : K) ≠ 0 ∧ f * (h : K) = (g : K)) →
    (f ∈ O ↔ ∃ g h : ↥S, ¬ (ϖ ∣ h) ∧ f * (h : K) = (g : K)) := by
  -- proof
  intro f hf
  obtain ⟨g, h, hh0, hfh⟩ := hf
  have hϖ0 : (ϖ : K) ≠ 0 := by
    intro h0
    refine hϖ.ne_zero (Subtype.ext h0)
  have hϖm : (⟨((ϖ : ↥S) : K), hSO ϖ⟩ : ↥O) ∈ maximalIdeal ↥O := (hcen ϖ).mpr (dvd_refl ϖ)
  constructor
  ·
    intro hfO
    if hg0 : g = 0 then
      refine ⟨0, 1, fun hd => hϖ.not_isUnit (isUnit_of_dvd_one hd), ?_⟩
      have hf0 : f = 0 := by
        have hzero : f * (h : K) = 0 := by
          rw [hfh, hg0]
          rfl
        cases mul_eq_zero.mp hzero
        ·
          rename_i h1
          refine h1
        ·
          rename_i h1
          refine absurd h1 hh0
      simp [hf0]
    else
      have hh0' : h ≠ 0 := by
        intro h0
        subst h0
        refine hh0 rfl
      obtain ⟨a, g', hg'nd, hg'⟩ := WfDvdMonoid.max_power_factor hg0 hϖ.irreducible
      obtain ⟨b, h', hh'nd, hh'⟩ := WfDvdMonoid.max_power_factor hh0' hϖ.irreducible
      have key : f * (ϖ : K) ^ b * (h' : K) = (ϖ : K) ^ a * (g' : K) := by
        have := hfh
        rw [hg', hh'] at this
        push_cast at this
        linear_combination this
      if hab : b ≤ a then
        refine ⟨ϖ ^ (a - b) * g', h', hh'nd, ?_⟩
        push_cast
        have hpow : (ϖ : K) ^ a = (ϖ : K) ^ b * (ϖ : K) ^ (a - b) := by
          rw [← pow_add, Nat.add_sub_cancel' hab]
        apply mul_left_cancel₀ (pow_ne_zero _ hϖ0)
        linear_combination key + (g' : K) * hpow
      else
        exfalso
        apply hg'nd
        have hlt : a < b := Nat.lt_of_not_le hab
        have hpow : (ϖ : K) ^ b = (ϖ : K) ^ a * (ϖ : K) ^ (b - a) := by
          rw [← pow_add, Nat.add_sub_cancel' hlt.le]
        have ha0 : (ϖ : K) ^ a ≠ 0 := pow_ne_zero _ hϖ0
        have hg'eq : (g' : K) = f * (h' : K) * (ϖ : K) ^ (b - a) := by
          apply mul_left_cancel₀ ha0
          linear_combination -key + (f * (h' : K)) * hpow
        have hmem : (⟨(g' : K), hSO g'⟩ : ↥O) =
            ⟨f, hfO⟩ * ⟨(h' : K), hSO h'⟩ * (⟨((ϖ : ↥S) : K), hSO ϖ⟩ : ↥O) ^ (b - a) := by
          apply Subtype.ext
          simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow]
          refine hg'eq
        rw [← hcen, hmem]
        apply Ideal.mul_mem_left
        refine Ideal.pow_mem_of_mem _ hϖm _ (Nat.sub_pos_of_lt hlt)
  ·
    intro hfmem
    obtain ⟨g', h', hnd, hfh'⟩ := hfmem
    have hunit : IsUnit (⟨(h' : K), hSO h'⟩ : ↥O) := by
      by_contra hnu
      refine hnd ((hcen h').mp ((IsLocalRing.mem_maximalIdeal _).mpr hnu))
    have hh'0 : (h' : K) ≠ 0 := by
      intro h0
      apply hunit.ne_zero
      refine Subtype.ext h0
    have hinv : ((h' : K))⁻¹ ∈ O := Submonoid.inv_mem_of_isUnit hunit
    have hf : f = (g' : K) * ((h' : K))⁻¹ := by
      rw [← hfh', mul_assoc, mul_inv_cancel₀ hh'0, mul_one]
    rw [hf]
    refine O.mul_mem _ _ (hSO g') hinv


-- created on 2026-10-20
