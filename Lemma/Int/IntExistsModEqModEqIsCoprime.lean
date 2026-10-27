import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma triple_of_modEq
  {n c d d' : ℤ}
  -- given
  (h : ∃ x y z : ℤ, x * c + y * d + z * n = 1)
  (hd : d' ≡ d [ZMOD n]) :
  -- imply
  ∃ x y z : ℤ, x * c + y * d' + z * n = 1 := by
  -- proof
  obtain ⟨x, y, z, hxyz⟩ := h
  obtain ⟨t, ht⟩ := Iff.mp Int.modEq_iff_dvd hd.symm
  exact ⟨x, y, z - y * t, by linear_combination hxyz + y * ht⟩

private lemma not_dvd_n_of_dvd
  {n c d p : ℤ}
  -- given
  (hp : Prime p)
  (h : ∃ x y z : ℤ, x * c + y * d + z * n = 1)
  (hpc : p ∣ c)
  (hpd : p ∣ d) :
  -- imply
  ¬ p ∣ n := by
  -- proof
  rintro hpn
  obtain ⟨x, y, z, hxyz⟩ := h
  apply hp.not_isUnit (isUnit_of_dvd_one _)
  rw [← hxyz]
  apply dvd_add (dvd_add (dvd_mul_of_dvd_right hpc x) (dvd_mul_of_dvd_right hpd y)) (dvd_mul_of_dvd_right hpn z)

private lemma exists_of_ne_zero
  {n c d : ℤ}
  -- given
  (hd : d ≠ 0)
  (h : ∃ x y z : ℤ, x * c + y * d + z * n = 1) :
  -- imply
  ∃ c' : ℤ, c' ≡ c [ZMOD n] ∧ IsCoprime c' d := by
  -- proof
  classical
  set S : Finset ℕ := d.natAbs.primeFactors.filter (fun p => ¬ (p : ℤ) ∣ c) with hS
  set m : ℤ := ∏ p ∈ S, (p : ℤ) with hm
  refine ⟨c + n * m, ?_, ?_⟩
  · apply Iff.mpr Int.modEq_iff_dvd ⟨-m, by ring⟩
  ·
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
    change Nat.Coprime d.natAbs (c + n * m).natAbs
    refine Nat.Coprime.symm (Nat.coprime_of_dvd fun p hp hpc' hpd => ?_)
    have hpZ : Prime (p : ℤ) := Iff.mp Nat.prime_iff_prime_int hp
    have hpd' : (p : ℤ) ∣ d := Iff.mpr Int.natCast_dvd hpd
    have hpc'Z : (p : ℤ) ∣ c + n * m := Iff.mpr Int.natCast_dvd hpc'
    if hpc : (p : ℤ) ∣ c then
      suffices hnm : (p : ℤ) ∣ n * m by
        apply (hpZ.dvd_or_dvd hnm).elim (not_dvd_n_of_dvd hpZ h hpc hpd') _
        rw [hm, hpZ.dvd_finsetProd_iff]
        rintro ⟨q, hq, hpq⟩
        rw [hS, Finset.mem_filter] at hq
        apply hq.2 (_ ▸ hpc)
        apply Iff.mp (Nat.prime_dvd_prime_iff_eq hp (Nat.prime_of_mem_primeFactors hq.1)) (Iff.mp Int.natCast_dvd_natCast hpq)
      have h2 := dvd_sub hpc'Z hpc
      rwa [add_sub_cancel_left] at h2
    else
      have hpS : p ∈ S := by
        rw [hS, Finset.mem_filter, Nat.mem_primeFactors]
        apply And.intro ⟨hp, hpd, Int.natAbs_ne_zero.mpr hd⟩ hpc
      have hpm : (p : ℤ) ∣ m := hm ▸ Finset.dvd_prod_of_mem _ hpS
      have : (p : ℤ) ∣ c := by
        have h2 : (p : ℤ) ∣ n * m := dvd_mul_of_dvd_right hpm n
        have h3 := dvd_sub hpc'Z h2
        rwa [add_sub_cancel_right] at h3
      apply hpc this

private lemma exists_modEq_and_modEq_and_isCoprime_impl
  {n c d : ℤ}
  -- given
  (h : ∃ x y z : ℤ, x * c + y * d + z * n = 1) :
  -- imply
  ∃ c' d' : ℤ, c' ≡ c [ZMOD n] ∧ d' ≡ d [ZMOD n] ∧ IsCoprime c' d' := by
  -- proof
  if hn : n = 0 then
    subst hn
    obtain ⟨x, y, z, hxyz⟩ := h
    exact ⟨c, d, Int.ModEq.refl c, Int.ModEq.refl d, x, y, by linear_combination hxyz⟩
  else
    obtain ⟨d', hd'd, hd'0⟩ : ∃ d' : ℤ, d' ≡ d [ZMOD n] ∧ d' ≠ 0 := by
      if hd : d = 0 then
        refine ⟨n, ?_, hn⟩
        rw [hd]
        apply Iff.mpr Int.modEq_iff_dvd ⟨-1, by ring⟩
      else
        exact ⟨d, Int.ModEq.refl d, hd⟩
    obtain ⟨c', hc'c, hcop⟩ := exists_of_ne_zero hd'0 (triple_of_modEq h hd'd)
    exact ⟨c', d', hc'c, hd'd, hcop⟩

/--
[Int_exists_modEq_and_modEq_and_isCoprime](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Int_exists_modEq_and_modEq_and_isCoprime.lean)
-/
@[path]
private lemma main
  {n c d : ℤ}
  -- given
  (h : ∃ x y z : ℤ, x * c + y * d + z * n = 1) :
  -- imply
  ∃ c' d' : ℤ, c' ≡ c [ZMOD n] ∧ d' ≡ d [ZMOD n] ∧ IsCoprime c' d' := by
  -- proof
  apply exists_modEq_and_modEq_and_isCoprime_impl h


-- created on 2026-10-20
