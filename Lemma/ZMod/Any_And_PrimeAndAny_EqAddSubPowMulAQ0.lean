import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma exists_prime_gt_and_quadratic_root
  {a q : ℤ}
  {N : ℕ}
  -- given
  (hq : 1 ≤ q) :
  -- imply
  ∃ r : ℕ, N < r ∧ r.Prime ∧ ∃ c : ZMod r, c ^ 2 - (a : ZMod r) * c + (q : ZMod r) = 0 := by
  -- proof
  classical
  set P : ℕ := (N + 3).factorial with hPdef
  have hP6 : 6 ≤ P := by
    have h3 : 3 ≤ N + 3 := by
      omega
    have h6 : Nat.factorial 3 ≤ (N + 3).factorial := Nat.factorial_le h3
    rw [hPdef]
    simpa [Nat.factorial] using h6
  have hP1 : 1 ≤ P := by
    omega
  have hPz : (1 : ℤ) ≤ (P : ℤ) := by
    exact_mod_cast hP1
  set t : ℤ := |a| + 2
  have ht2 : 2 ≤ t := by
    have _ := abs_nonneg a
    omega
  have hta : a < t := by
    have _ := le_abs_self a
    omega
  set h : ℤ := q * (P : ℤ) ^ 2 * t ^ 2 - a * (P : ℤ) * t + 1 with hhdef
  have hmodP : h - (P : ℤ) * (q * (P : ℤ) * t ^ 2 - a * t) = 1 := by
    rw [hhdef]
    ring
  have hPt : (0 : ℤ) < (P : ℤ) * t := mul_pos (by linarith [hPz] : (0 : ℤ) < (P : ℤ)) (by linarith [ht2] : (0 : ℤ) < t)
  have hne1 : h ≠ 1 := by
    intro h1
    have hzero : (P : ℤ) * t * (q * (P : ℤ) * t - a) = 0 := by
      have hsub : h - 1 = 0 := by
        omega
      rw [hhdef] at hsub
      linear_combination hsub
    have hfac : q * (P : ℤ) * t - a = 0 := by
      obtain h' | h' := Iff.mp mul_eq_zero hzero
      · apply absurd h' (ne_of_gt hPt)
      · apply h'
    nlinarith [mul_nonneg (by linarith [hq] : (0 : ℤ) ≤ q - 1) (le_of_lt hPt), mul_nonneg (by linarith [hPz] : (0 : ℤ) ≤ (P : ℤ) - 1) (by linarith [ht2] : (0 : ℤ) ≤ t), hta, hfac]
  have hnem1 : h ≠ -1 := by
    intro h1
    have hdvd2 : (P : ℤ) ∣ 2 := ⟨-(q * (P : ℤ) * t ^ 2 - a * t), by linear_combination - hmodP + h1⟩
    have h2 : (P : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) hdvd2
    have h6 : (6 : ℤ) ≤ (P : ℤ) := by
      exact_mod_cast hP6
    omega
  have habs : h.natAbs ≠ 1 := by
    omega
  obtain ⟨r, hrprime, hrdvd⟩ := Nat.exists_prime_and_dvd habs
  have hrdvdh : (r : ℤ) ∣ h := (Iff.mpr Int.natCast_dvd_natCast hrdvd).trans (Iff.mpr Int.natAbs_dvd dvd_rfl)
  refine ⟨r, ?_, hrprime, ?_⟩
  ·
    by_contra hle
    have hle' : r ≤ N := Iff.mp not_lt hle
    have hrP : (r : ℤ) ∣ (P : ℤ) := by
      exact_mod_cast Nat.dvd_factorial hrprime.pos (by omega)
    have hr1 : (r : ℤ) ∣ 1 := by
      have := dvd_sub hrdvdh (Dvd.dvd.mul_right hrP (q * (P : ℤ) * t ^ 2 - a * t))
      rwa [hmodP] at this
    apply hrprime.one_lt.ne' (Iff.mp Nat.dvd_one _)
    exact_mod_cast hr1
  ·
    set n₀ : ℤ := q * (P : ℤ) * t with hn₀
    have hval : n₀ ^ 2 - a * n₀ + q = q * h := by
      rw [hn₀, hhdef]
      ring
    have hdvdval : (r : ℤ) ∣ n₀ ^ 2 - a * n₀ + q := by
      rw [hval]
      apply Dvd.dvd.mul_left hrdvdh q
    refine ⟨(n₀ : ZMod r), ?_⟩
    have hcast : ((n₀ ^ 2 - a * n₀ + q : ℤ) : ZMod r) = 0 := Iff.mpr (ZMod.intCast_zmod_eq_zero_iff_dvd _ r) hdvdval
    push_cast at hcast
    linear_combination hcast

/--
[FrobeniusEndo_exists_prime_gt_and_quadratic_root](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_FrobeniusEndo_exists_prime_gt_and_quadratic_root.lean)
-/
@[path]
private lemma main
  {a q : ℤ}
  {N : ℕ}
  -- given
  (hq : 1 ≤ q) :
  -- imply
  ∃ r : ℕ, N < r ∧ r.Prime ∧ ∃ c : ZMod r, c ^ 2 - (a : ZMod r) * c + (q : ZMod r) = 0 := by
  -- proof
  apply exists_prime_gt_and_quadratic_root hq


-- created on 2026-10-20
