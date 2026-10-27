import Mathlib
import Initialize.Tactic.Attr.Basic
open UniqueFactorizationMonoid


/--
[UniqueFactorizationMonoid_exists_eq_unit_mul_pow_mul_pow_of_forall_dvd_multiplicity](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_UniqueFactorizationMonoid_exists_eq_unit_mul_pow_mul_pow_of_forall_dvd_multiplicity.lean)
-/
@[path]
private lemma main
  [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
  {s : R}
  {e : ℕ}
  {f : R}
-- given
  (hs : Prime s)
  (he : 0 < e)
  (hf : f ≠ 0)
  (hdiv : ∀ p : R, Prime p → ¬ Associated p s → e ∣ multiplicity p f) :
-- imply
  ∃ (w : Rˣ) (k : ℕ) (g : R), f = (w : R) * s ^ k * g ^ e := by
-- proof
  classical
    let : StrongNormalizationMonoid R := UniqueFactorizationMonoid.strongNormalizationMonoid
    set M : Multiset R := normalizedFactors f with hM
    set s₀ : R := normalize s with hs₀
    set T : Finset R := M.toFinset with hT
    have hcount : ∀ q ∈ T.erase s₀, e ∣ M.count q := by
      intro q hq
      have hqT : q ∈ T := Finset.mem_of_mem_erase hq
      have hqM : q ∈ normalizedFactors f := by rwa [hT, Multiset.mem_toFinset] at hqT
      have hqprime : Prime q := prime_of_normalized_factor q hqM
      have hqnorm : normalize q = q := normalize_normalized_factor q hqM
      have hna : ¬ Associated q s := by
        intro h
        apply Finset.ne_of_mem_erase hq
        rw [← hqnorm, hs₀]
        apply normalize_eq_normalize_iff.mpr ⟨h.dvd, h.symm.dvd⟩
      have := hdiv q hqprime hna
      rwa [multiplicity_eq_count_normalizedFactors hqprime.irreducible hf, hqnorm] at this
    refine ?_
    let g : R := ∏ q ∈ T.erase s₀, q ^ (M.count q / e)
    have hge : g ^ e = ∏ q ∈ T.erase s₀, q ^ M.count q := by
      rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl fun q hq => ?_
      rw [← pow_mul, Nat.div_mul_cancel (hcount q hq)]
    have hprod : M.prod = s₀ ^ M.count s₀ * g ^ e := by
      rw [Finset.prod_multiset_count, hge]
      if hsT : s₀ ∈ T then
        rw [← Finset.mul_prod_erase T (fun q => q ^ M.count q) hsT]
      else
        have h0 : M.count s₀ = 0 := Multiset.count_eq_zero_of_notMem (by rwa [hT, Multiset.mem_toFinset] at hsT)
        rw [h0, pow_zero, one_mul, Finset.erase_eq_of_notMem hsT]
    obtain ⟨u, hu⟩ := prod_normalizedFactors hf
    obtain ⟨v, hv⟩ := associated_normalize s
    refine ⟨u * v ^ M.count s₀, M.count s₀, g, ?_⟩
    rw [← hu, ← hM, hprod, hs₀, ← hv, Units.val_mul, Units.val_pow_eq_pow_val, mul_pow]
    ring


-- created on 2026-10-23
