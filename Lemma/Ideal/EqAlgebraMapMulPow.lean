import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[IsNoetherianRing_exists_unit_mul_zpow_eq_of_span_singleton_isPrime](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsNoetherianRing_exists_unit_mul_zpow_eq_of_span_singleton_isPrime.lean)
-/
@[path]
private lemma main
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    (π : A) (hπ : (Ideal.span {π}).IsPrime) (hπ0 : π ≠ 0)
    (a : K) (hab : ∃ (m : ℕ) (b : A), a * algebraMap A K π ^ m = algebraMap A K b)
    (hac : ∃ (m : ℕ) (c : A), a⁻¹ * algebraMap A K π ^ m = algebraMap A K c) (ha0 : a ≠ 0) :
    ∃ (n : ℤ) (u : Aˣ), a = algebraMap A K (u : A) * algebraMap A K π ^ n := by
  classical
  obtain ⟨m, b, hb⟩ := hab
  obtain ⟨m', c, hc⟩ := hac
  have hprime : Prime π := (Ideal.span_singleton_prime hπ0).mp hπ
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hP : algebraMap A K π ≠ 0 := fun h => hπ0 (hinj (by rw [h, map_zero]))
  have hbc : b * c = π ^ (m + m') := by
    apply hinj
    rw [map_mul, map_pow, ← hb, ← hc, pow_add]
    calc a * algebraMap A K π ^ m * (a⁻¹ * algebraMap A K π ^ m')
        = (a * a⁻¹) * (algebraMap A K π ^ m * algebraMap A K π ^ m') := by ring
      _ = algebraMap A K π ^ m * algebraMap A K π ^ m' := by rw [mul_inv_cancel₀ ha0, one_mul]
  have hb0 : b ≠ 0 := by
    intro h; rw [h, zero_mul] at hbc; exact pow_ne_zero _ hπ0 hbc.symm
  have hc0 : c ≠ 0 := by
    intro h; rw [h, mul_zero] at hbc; exact pow_ne_zero _ hπ0 hbc.symm
  obtain ⟨i, b₀, hb₀, rfl⟩ := WfDvdMonoid.max_power_factor' hb0 hprime.not_unit
  obtain ⟨j, c₀, hc₀, rfl⟩ := WfDvdMonoid.max_power_factor' hc0 hprime.not_unit
  have hkey : π ^ (i + j) * (b₀ * c₀) = π ^ (m + m') := by
    rw [← hbc]; ring
  have hndvd : ¬ π ∣ b₀ * c₀ := fun h => (hprime.dvd_or_dvd h).elim hb₀ hc₀
  have hunit : b₀ * c₀ = 1 := by
    rcases le_total (i + j) (m + m') with hle | hle
    · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
      rw [hd, pow_add π (i + j) d] at hkey
      have h1 : b₀ * c₀ = π ^ d := mul_left_cancel₀ (pow_ne_zero _ hπ0) hkey
      rcases Nat.eq_zero_or_pos d with hd0 | hdpos
      · rw [h1, hd0, pow_zero]
      · exact absurd (h1 ▸ dvd_pow_self π hdpos.ne') hndvd
    · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
      rw [hd, pow_add π (m + m') d, mul_assoc] at hkey
      have h1 : π ^ d * (b₀ * c₀) = 1 := mul_left_cancel₀ (pow_ne_zero _ hπ0) (hkey.trans (mul_one _).symm)
      rcases Nat.eq_zero_or_pos d with hd0 | hdpos
      · rw [hd0, pow_zero, one_mul] at h1; exact h1
      · exfalso
        apply hprime.not_unit
        exact isUnit_of_dvd_one (Dvd.dvd.trans (dvd_pow_self π hdpos.ne') (Dvd.intro _ h1))
  refine ⟨(i : ℤ) - (m : ℤ), Units.mkOfMulEqOne b₀ c₀ hunit, ?_⟩
  rw [Units.val_mkOfMulEqOne]
  have ha : a = algebraMap A K (π ^ i * b₀) / algebraMap A K π ^ m := by
    rw [eq_div_iff (pow_ne_zero _ hP), hb]
  rw [ha, map_mul, map_pow, zpow_sub₀ hP, zpow_natCast, zpow_natCast, div_eq_mul_inv, div_eq_mul_inv]
  ring

-- created on 2026-10-20
