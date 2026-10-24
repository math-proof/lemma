import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma charP_of_coeff {K : Type u} [CommRing K] (ℓ : ℕ) [CharP K ℓ] : CharP (LaurentSeries K) ℓ := charP_of_injective_ringHom (HahnSeries.C_injective (Γ := ℤ) (R := K)) ℓ

private lemma coeff_pow_ringChar_eq_zero_of_not_dvd {K : Type u} [CommRing K] (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ] (g : LaurentSeries K) (n : ℤ) (hn : ¬ (ℓ : ℤ) ∣ n) : (g ^ ℓ).coeff n = 0 := by
  classical
  let _ := charP_of_coeff (K := K) ℓ
  have hℓpos : 0 < ℓ := (Fact.out : ℓ.Prime).pos
  set M : ℤ := max (n + 1) 0 with hM
  have hMn : n < (ℓ : ℤ) * M := by
    obtain h | h := le_or_gt 0 (n + 1)
    ·
      have hM' : M = n + 1 := max_eq_left h
      have h1 : (1 : ℤ) ≤ ℓ := by exact_mod_cast hℓpos
      nlinarith
    ·
      have hM' : M = 0 := max_eq_right (le_of_lt h)
      rw [hM', mul_zero]
      linarith
  set H : LaurentSeries K := ∑ k ∈ Finset.Ico g.order M, HahnSeries.single k (g.coeff k) with hH
  set T : LaurentSeries K := g - H with hT
  have hHcoeff : ∀ k : ℤ, H.coeff k = if k ∈ Finset.Ico g.order M then g.coeff k else 0 := by
    intro k
    rw [hH, HahnSeries.coeff_sum]
    simp_rw [HahnSeries.coeff_single]
    if hk : k ∈ Finset.Ico g.order M then
      rw [ite_eq_left hk, Finset.sum_eq_single k]
      ·
        rw [ite_eq_left rfl]
      ·
        intro b _ hb
        refine ite_eq_right fun h => hb h.symm
      ·
        intro hk'
        apply absurd hk hk'
    else
      rw [ite_eq_right hk]
      apply Finset.sum_eq_zero
      intro b hb
      refine ite_eq_right fun h => ?_
      rw [h] at hk
      apply hk hb
  have hTcoeff : ∀ k : ℤ, k < M → T.coeff k = 0 := by
    intro k hk
    rw [hT, HahnSeries.coeff_sub, hHcoeff]
    split_ifs with hmem
    ·
      apply sub_self
    ·
      rw [Finset.mem_Ico, not_and_or, not_le] at hmem
      obtain hlt | hge := hmem
      ·
        if hg : g = 0 then
          simp [hg]
        else
          rw [HahnSeries.coeff_eq_zero_of_lt_order hlt, sub_zero]
      ·
        apply absurd hk (not_lt.mpr (le_of_not_gt hge))
  have hTtop : ((M : ℤ) : WithTop ℤ) ≤ T.orderTop := HahnSeries.le_orderTop_iff_forall.mpr fun j hj => hTcoeff j (WithTop.coe_lt_coe.mp hj)
  have hTpow : (T ^ ℓ).coeff n = 0 := by
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    refine lt_of_lt_of_le ?_ HahnSeries.orderTop_nsmul_le_orderTop_pow
    refine lt_of_lt_of_le ?_ (nsmul_le_nsmul_right hTtop ℓ)
    rw [← WithTop.coe_nsmul, WithTop.coe_lt_coe, nsmul_eq_mul]
    apply hMn
  have hHpow : (H ^ ℓ).coeff n = 0 := by
    rw [hH, sum_pow_char]
    simp_rw [HahnSeries.single_pow]
    rw [HahnSeries.coeff_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [HahnSeries.coeff_single_of_ne]
    intro hnk
    apply hn
    rw [hnk, ← natCast_zsmul, smul_eq_mul]
    apply dvd_mul_right _ _
  have hg : g = H + T := by rw [hT, add_sub_cancel]
  rw [hg, add_pow_char, HahnSeries.coeff_add, hHpow, hTpow, add_zero]

/--
[LaurentSeries_coeff_pow_ringChar_eq_zero_of_not_dvd](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LaurentSeries_coeff_pow_ringChar_eq_zero_of_not_dvd.lean)
-/
@[path]
private lemma main
  {K : Type u} [CommRing K]
  (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]
  (g : LaurentSeries K) (n : ℤ) (hn : ¬ (ℓ : ℤ) ∣ n) :
  -- imply
  (g ^ ℓ).coeff n = 0 :=
  coeff_pow_ringChar_eq_zero_of_not_dvd ℓ g n hn


-- created on 2026-10-20
