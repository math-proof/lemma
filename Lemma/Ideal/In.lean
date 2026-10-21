import Mathlib
import sympy.Basic
open IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[IsLocalRing_mem_of_mul_sq_sub_intCast_mem_of_forall_charZero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_mem_of_mul_sq_sub_intCast_mem_of_forall_charZero.lean)
-/
@[path]
private lemma main
  {R : Type} [CommRing R] [IsLocalRing R]
  (r : R)
  (d : ℤ)
  (𝔭 : Ideal R)
  -- given
  (hmax : r ∈ maximalIdeal R)
  (hquad : ∀ 𝔭 : Ideal R, 𝔭.IsPrime → r * (r ^ 2 - (d : R)) ∈ 𝔭)
  (hzero : ∀ 𝔭 : Ideal R, 𝔭.IsPrime → CharZero (R ⧸ 𝔭) → r ∈ 𝔭)
  (h𝔭 : 𝔭.IsPrime) :
  -- imply
  r ∈ 𝔭 := by
  -- proof
  classical
  obtain h | h := h𝔭.mem_or_mem (hquad 𝔭 h𝔭)
  · apply h
  have hle : 𝔭 ≤ maximalIdeal R := le_maximalIdeal h𝔭.ne_top
  have hdm : (d : R) ∈ maximalIdeal R := by
    have h1 : r ^ 2 - (d : R) ∈ maximalIdeal R := hle h
    have h2 : r ^ 2 ∈ maximalIdeal R := Ideal.pow_mem_of_mem _ hmax 2 (by norm_num)
    have h3 := Ideal.sub_mem _ h2 h1
    simpa using h3
  let _ : 𝔭.IsPrime := h𝔭
  obtain ⟨p, hp⟩ := CharP.exists (R ⧸ 𝔭)
  obtain hpp | hp0 := CharP.char_is_prime_or_zero (R ⧸ 𝔭) p
  ·
    have hpmem : (p : R) ∈ 𝔭 := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      apply CharP.cast_eq_zero (R ⧸ 𝔭) p
    have hpd : (p : ℤ) ∣ d := by
      by_contra hnd
      have hirr : Irreducible (p : ℤ) := (Nat.prime_iff_prime_int.mp hpp).irreducible
      have hcop : IsCoprime (p : ℤ) d := (Irreducible.coprime_iff_not_dvd hirr).mpr hnd
      obtain ⟨u, v, huv⟩ := hcop
      apply (Ideal.ne_top_iff_one _).mp (maximalIdeal.isMaximal R).ne_top
      ·
        have : ((u * p + v * d : ℤ) : R) ∈ maximalIdeal R := by
          push_cast
          apply Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hle hpmem)) (Ideal.mul_mem_left _ _ hdm)
        rw [huv, Int.cast_one] at this
        apply this
    obtain ⟨e, he⟩ := hpd
    have hdp : (d : R) ∈ 𝔭 := by
      rw [he]
      push_cast
      apply Ideal.mul_mem_right _ _ hpmem
    apply h𝔭.mem_of_pow_mem 2
    ·
      have := Ideal.add_mem _ h hdp
      simpa using this
  ·
    subst hp0
    let _ : CharZero (R ⧸ 𝔭) := CharP.charP_to_charZero (R ⧸ 𝔭)
    apply hzero 𝔭 h𝔭 inferInstance


-- created on 2026-10-20
