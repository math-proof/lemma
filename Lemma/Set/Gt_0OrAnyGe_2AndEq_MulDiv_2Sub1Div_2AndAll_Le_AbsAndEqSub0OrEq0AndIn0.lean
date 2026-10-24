import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma helper_main (lam : ℝ) (S : Set ℤ) (hS : S.Nonempty) (hminus : ∀ n ∈ S, 0 ≤ 4 * lam + n * (n - 2)) (hplus : ∀ n ∈ S, 0 ≤ 4 * lam + n * (n + 2)) (clminus : ∀ n ∈ S, 0 < 4 * lam + n * (n - 2) → n - 2 ∈ S) (clplus : ∀ n ∈ S, 0 < 4 * lam + n * (n + 2) → n + 2 ∈ S) : 0 < lam ∨ (∃ k₀ : ℕ, 2 ≤ k₀ ∧ lam = ((k₀ : ℝ) / 2) * (1 - (k₀ : ℝ) / 2) ∧ ∀ n ∈ S, (k₀ : ℤ) ≤ |n| ∧ (n - k₀) % 2 = 0) ∨ (lam = 0 ∧ (0 : ℤ) ∈ S) := by
  classical
  if hpos : 0 < lam then
    apply Or.inl hpos
  else
    push Not at hpos
    if h0 : (0 : ℤ) ∈ S then
      refine Or.inr (Or.inr ⟨?_, h0⟩)
      have := hminus 0 h0
      push_cast at this
      linarith
    else
      have h1 : (1 : ℤ) ∉ S := by
        intro h
        have := hminus 1 h
        push_cast at this
        linarith
      have h1' : (-1 : ℤ) ∉ S := by
        intro h
        have := hplus (-1) h
        push_cast at this
        linarith
      have hex : ∃ k : ℕ, ∃ n ∈ S, n.natAbs = k := by
        obtain ⟨n, hn⟩ := hS
        exact ⟨n.natAbs, n, hn, rfl⟩
      set k₀ := Nat.find hex with hk₀
      obtain ⟨n₀, hn₀S, hn₀⟩ := Nat.find_spec hex
      have hmin : ∀ m ∈ S, k₀ ≤ m.natAbs := by
        intro m hm
        by_contra hlt
        push Not at hlt
        apply Nat.find_min hex hlt ⟨m, hm, rfl⟩
      rw [← hk₀] at hn₀
      have hk2 : 2 ≤ k₀ := by
        by_contra hlt
        push Not at hlt
        interval_cases k₀
        ·
          have : n₀ = 0 := Int.natAbs_eq_zero.mp hn₀
          apply h0 (this ▸ hn₀S)
        ·
          obtain h | h := Int.natAbs_eq_iff.mp hn₀
          · apply h1 (by simpa [h] using hn₀S)
          · apply h1' (by simpa [h] using hn₀S)
      have hkey : 4 * lam + (k₀ : ℝ) * ((k₀ : ℝ) - 2) = 0 := by
        obtain h | h := Int.natAbs_eq_iff.mp hn₀
        ·
          have hge := hminus n₀ hn₀S
          rw [h] at hge
          push_cast at hge
          by_contra hne
          have hposE : 0 < 4 * lam + (n₀ : ℝ) * ((n₀ : ℝ) - 2) := by
            rw [h]
            push_cast
            apply lt_of_le_of_ne hge (Ne.symm hne)
          have hmem := clminus n₀ hn₀S (by exact_mod_cast hposE)
          have := hmin _ hmem
          rw [h] at this
          omega
        ·
          have hge := hplus n₀ hn₀S
          rw [h] at hge
          push_cast at hge
          by_contra hne
          have hne' : 4 * lam + (-(k₀ : ℝ)) * (-(k₀ : ℝ) + 2) ≠ 0 := by
            intro h'
            apply hne
            linarith
          have hposE : 0 < 4 * lam + (n₀ : ℝ) * ((n₀ : ℝ) + 2) := by
            rw [h]
            push_cast
            apply lt_of_le_of_ne hge (Ne.symm hne')
          have hmem := clplus n₀ hn₀S (by exact_mod_cast hposE)
          have := hmin _ hmem
          rw [h] at this
          omega
      refine Or.inr (Or.inl ⟨k₀, hk2, by linarith [hkey], fun m hm => ⟨?_, ?_⟩⟩)
      ·
        have := hmin m hm
        rw [← Int.natCast_natAbs]
        exact_mod_cast this
      ·
        have hE : ∀ m : ℤ, 4 * lam + (m : ℝ) * ((m : ℝ) - 2) = ((m * (m - 2) - (k₀ : ℤ) * ((k₀ : ℤ) - 2) : ℤ) : ℝ) := by
          intro m
          push_cast
          linarith [hkey]
        have hE' : ∀ m : ℤ, 4 * lam + (m : ℝ) * ((m : ℝ) + 2) = ((m * (m + 2) - (k₀ : ℤ) * ((k₀ : ℤ) - 2) : ℤ) : ℝ) := by
          intro m
          push_cast
          linarith [hkey]
        suffices H : ∀ d : ℕ, ∀ m ∈ S, m.natAbs = k₀ + d → (m - k₀) % 2 = 0 by
          obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (hmin m hm)
          apply H d m hm hd
        intro d
        refine Nat.strong_induction_on d ?_
        intro d IH m hm hd
        obtain hd2 | hd2 := Nat.lt_or_ge d 2
        ·
          interval_cases d
          ·
            obtain h | h := Int.natAbs_eq_iff.mp hd
            ·
              rw [h]
              push_cast
              omega
            ·
              rw [h]
              push_cast
              omega
          ·
            exfalso
            obtain h | h := Int.natAbs_eq_iff.mp hd
            ·
              have hineq : (0 : ℤ) < m * (m - 2) - k₀ * (k₀ - 2) := by
                rw [h]
                push_cast
                nlinarith
              have hp : 0 < 4 * lam + (m : ℝ) * ((m : ℝ) - 2) := by
                rw [hE]
                exact_mod_cast hineq
              have hmem := clminus m hm hp
              have := hmin _ hmem
              rw [h] at this
              push_cast at this
              omega
            ·
              have hineq : (0 : ℤ) < m * (m + 2) - k₀ * (k₀ - 2) := by
                rw [h]
                push_cast
                nlinarith
              have hp : 0 < 4 * lam + (m : ℝ) * ((m : ℝ) + 2) := by
                rw [hE']
                exact_mod_cast hineq
              have hmem := clplus m hm hp
              have := hmin _ hmem
              rw [h] at this
              push_cast at this
              omega
        ·
          obtain h | h := Int.natAbs_eq_iff.mp hd
          ·
            have hineq : (0 : ℤ) < m * (m - 2) - k₀ * (k₀ - 2) := by
              rw [h]
              push_cast
              nlinarith
            have hp : 0 < 4 * lam + (m : ℝ) * ((m : ℝ) - 2) := by
              rw [hE]
              exact_mod_cast hineq
            have hmem := clminus m hm hp
            have hd' : (m - 2).natAbs = k₀ + (d - 2) := by
              rw [h]
              push_cast
              omega
            have := IH (d - 2) (by omega) (m - 2) hmem hd'
            omega
          ·
            have hineq : (0 : ℤ) < m * (m + 2) - k₀ * (k₀ - 2) := by
              rw [h]
              push_cast
              nlinarith
            have hp : 0 < 4 * lam + (m : ℝ) * ((m : ℝ) + 2) := by
              rw [hE']
              exact_mod_cast hineq
            have hmem := clplus m hm hp
            have hd' : (m + 2).natAbs = k₀ + (d - 2) := by
              rw [h]
              push_cast
              omega
            have := IH (d - 2) (by omega) (m + 2) hmem hd'
            omega
/--
[LanglandsTunnell_casimir_pos_or_discrete_or_zero_of_weightSet](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LanglandsTunnell_casimir_pos_or_discrete_or_zero_of_weightSet.lean)
-/
@[path]
private lemma main
  (lam : ℝ)
  (S : Set ℤ)
  -- given
  (hS : S.Nonempty)
  (hminus : ∀ n ∈ S, 0 ≤ 4 * lam + n * (n - 2))
  (hplus : ∀ n ∈ S, 0 ≤ 4 * lam + n * (n + 2))
  (clminus : ∀ n ∈ S, 0 < 4 * lam + n * (n - 2) → n - 2 ∈ S)
  (clplus : ∀ n ∈ S, 0 < 4 * lam + n * (n + 2) → n + 2 ∈ S) :
  -- imply
  0 < lam ∨ (∃ k₀ : ℕ, 2 ≤ k₀ ∧ lam = ((k₀ : ℝ) / 2) * (1 - (k₀ : ℝ) / 2) ∧ ∀ n ∈ S, (k₀ : ℤ) ≤ |n| ∧ (n - k₀) % 2 = 0) ∨ (lam = 0 ∧ (0 : ℤ) ∈ S) :=
  helper_main lam S hS hminus hplus clminus clplus


-- created on 2026-10-20
