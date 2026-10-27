import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.FormalHecke_Eigensystem
import Lemma.Int.P2MUtil
open FormalHecke


/-- ported from external source -/

private lemma _root_.FormalHecke.IsEigensystem.prime_pow'
  {R : Type*}
  [CommRing R]
  {e a : ℕ → R} (h : IsEigensystem e a) {ℓ : ℕ} (hℓ : ℓ.Prime)
  (r : ℕ) : a (ℓ ^ (r + 2)) = a ℓ * a (ℓ ^ (r + 1)) - e ℓ * a (ℓ ^ r) := by
  have key := h.2 ℓ hℓ (ℓ ^ (r + 1))
  have hdiv : ℓ ^ (r + 1) / ℓ = ℓ ^ r := by
    rw [pow_succ' ℓ r, Nat.mul_div_cancel_left _ hℓ.pos]
  rw [ite_eq_left (dvd_pow_self ℓ (Nat.succ_ne_zero r)), hdiv, ← pow_succ'] at key
  linear_combination key
p2m_export "FormalHecke" "IsEigensystem.prime_pow'"

private lemma _root_.FormalHecke.IsEigensystem.mul_coprime'
  {R : Type*}
  [CommRing R]
  {e a : ℕ → R} (h : IsEigensystem e a) :
  ∀ m n : ℕ, m.Coprime n → a (m * n) = a m * a n := by
  obtain ⟨h1, H⟩ := h
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro n hmn
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    ·
      rw [Nat.coprime_zero_left] at hmn
      subst hmn
      simp [h1]
    rcases eq_or_ne m 1 with rfl | hm1
    · simp [h1]
    obtain ⟨ℓ, hℓ, hdvd⟩ := Nat.exists_prime_and_dvd hm1
    obtain ⟨m₁, rfl⟩ := hdvd
    have hm₁0 : m₁ ≠ 0 := by rintro rfl; simp at hm0
    have hm₁_lt : m₁ < ℓ * m₁ :=
      (Nat.lt_mul_iff_one_lt_left (Nat.pos_of_ne_zero hm₁0)).mpr hℓ.one_lt
    have hcop_m₁n : m₁.Coprime n := Nat.Coprime.coprime_dvd_left (dvd_mul_left m₁ ℓ) hmn
    have hcop_ℓn : ℓ.Coprime n := Nat.Coprime.coprime_dvd_left (dvd_mul_right ℓ m₁) hmn
    have hℓn : ¬ ℓ ∣ n := (Nat.Prime.coprime_iff_not_dvd hℓ).mp hcop_ℓn
    by_cases hℓm₁ : ℓ ∣ m₁
    ·
      obtain ⟨m₂, rfl⟩ := hℓm₁
      have hm₂0 : m₂ ≠ 0 := by rintro rfl; simp at hm₁0
      have hm₂_lt : m₂ < ℓ * (ℓ * m₂) :=
        lt_of_le_of_lt (Nat.le_mul_of_pos_left m₂ hℓ.pos) hm₁_lt
      have hcop_m₂n : m₂.Coprime n :=
        Nat.Coprime.coprime_dvd_left (dvd_mul_left m₂ ℓ) hcop_m₁n
      have key₁ := H ℓ hℓ (ℓ * m₂ * n)
      have key₂ := H ℓ hℓ (ℓ * m₂)
      rw [ite_eq_left ⟨m₂ * n, by ring⟩, show ℓ * m₂ * n / ℓ = m₂ * n by
            rw [mul_assoc, Nat.mul_div_cancel_left _ hℓ.pos]] at key₁
      rw [ite_eq_left ⟨m₂, rfl⟩, Nat.mul_div_cancel_left _ hℓ.pos] at key₂
      rw [IH _ hm₁_lt n hcop_m₁n, IH _ hm₂_lt n hcop_m₂n] at key₁
      have : ℓ * (ℓ * m₂) * n = ℓ * (ℓ * m₂ * n) := by ring
      rw [this]
      linear_combination key₁ - a n * key₂
    ·
      have hℓm₁n : ¬ ℓ ∣ m₁ * n := fun hd => ((Nat.Prime.dvd_mul hℓ).mp hd).elim hℓm₁ hℓn
      have key₁ := H ℓ hℓ (m₁ * n)
      have key₂ := H ℓ hℓ m₁
      rw [ite_eq_right hℓm₁n, mul_zero, add_zero] at key₁
      rw [ite_eq_right hℓm₁, mul_zero, add_zero] at key₂
      rw [IH _ hm₁_lt n hcop_m₁n] at key₁
      have : ℓ * m₁ * n = ℓ * (m₁ * n) := by ring
      rw [this]
      linear_combination key₁ - a n * key₂
p2m_export "FormalHecke" "IsEigensystem.mul_coprime'"
@[path]
private lemma main
  [CommRing R]
  {e a : ℕ → R}
-- given
  (h : FormalHecke.IsEigensystem e a) :
-- imply
  FormalHecke.IsRecursive e a :=
-- proof
  ⟨h.1, h.mul_coprime', fun _ r hℓ => h.prime_pow' hℓ r⟩


-- created on 2026-10-23
