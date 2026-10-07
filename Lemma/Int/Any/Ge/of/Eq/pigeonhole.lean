import Mathlib.Data.Finset.Basic
import sympy.Basic
open Finset


@[main]
private lemma main
  {k : ℕ}
-- given
  (hk : 0 < k)
  {x : Fin k → ℕ}
  {n : ℕ}
  (h : ∑ i : Fin k, x i = n) :
-- imply
  ∃ i : Fin k, x i ≥ (n + k - 1) / k := by
-- proof
  by_contra h'
  push Not at h'
  have hn : 0 < n := by
    by_contra hn0
    have hn0' : n = 0 := by omega
    have hq0 : (n + k - 1) / k = 0 := by
      rw [hn0']
      rw [Nat.div_eq_zero_iff]
      omega
    have hcont := h' ⟨0, hk⟩
    rw [hq0] at hcont
    exact Nat.not_lt_zero (x ⟨0, hk⟩) hcont
  have hle : ∀ i : Fin k, x i ≤ (n + k - 1) / k - 1 := by
    intro i
    have hl : x i < (n + k - 1) / k := h' i
    exact Nat.le_pred_of_lt hl
  have hsum : ∑ i : Fin k, x i ≤ k * ((n + k - 1) / k - 1) := by
    have := Finset.sum_le_card_nsmul (s := Finset.univ) (f := x) (n := (n + k - 1) / k - 1)
      (fun i _ => hle i)
    simpa [Finset.card_fin] using this
  have hlt : k * ((n + k - 1) / k - 1) < n := by
    set q := (n + k - 1) / k
    set r := (n + k - 1) % k
    have hmod : k * q + r = n + k - 1 := by
      simpa [q, r] using Nat.div_add_mod (n + k - 1) k
    have hr : r < k := by simpa [r] using Nat.mod_lt (n + k - 1) hk
    have hq1 : 1 ≤ q := by
      simpa [q] using Nat.le_div_iff_mul_le (by omega) |>.mpr (by omega)
    have hnm1 : 0 ≤ n - 1 := by omega
    have hrn : r ≤ n - 1 := by
      have hr2 : r = (n - 1) % k := by
        simp only [r]
        have h2 : n + k - 1 = n - 1 + k := by omega
        rw [h2, Nat.add_mod_right]
      rw [hr2]
      exact Nat.mod_le (n - 1) k
    have hkq : k * q ≥ k := by
      have : k * q ≥ k * 1 := Nat.mul_le_mul_left k hq1
      simpa using this
    have hsub1 : k * (q - 1) = k * q - k := by
      rw [Nat.mul_sub_left_distrib]
      simp
    have h1 : k * q = n + k - 1 - r := by omega
    have h2 : n + k - 1 - r ≥ k := by omega
    rw [hsub1, h1]
    have h3 : n + k - 1 - r - k = n - 1 - r := by omega
    rw [h3]
    omega
  rw [h] at hsum
  exact not_le.mpr hlt hsum


-- created on 2022-07-06
