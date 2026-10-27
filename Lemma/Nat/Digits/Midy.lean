import Mathlib
import Initialize.Tactic.Attr.Basic


namespace MetaMathlibExt

/--
[midy_theorem_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Digits/Midy.lean)
-/
@[path]
lemma midy_theorem_general
  {p n : ℕ}
-- given
  (hp : Nat.Prime p)
  (hdiv : p ∣ 10 ^ (2 * n) - 1)
  (hnot : ¬p ∣ 10 ^ n - 1) :
-- imply
  Nat.ofDigits 10 (List.take n (Nat.digits 10 ((10 ^ (2 * n) - 1) / p))) +
    Nat.ofDigits 10 (List.drop n (Nat.digits 10 ((10 ^ (2 * n) - 1) / p))) =
    10 ^ n - 1 := by
-- proof
  have hn : 0 < n := Nat.pos_of_ne_zero fun h => hnot (by simp [h])
  have hp_pos : 0 < p := hp.pos
  have hp2 : 2 ≤ p := hp.two_le
  have hA1 : 1 ≤ 10 ^ n := Nat.one_le_pow n 10 (by norm_num)
  have hA10 : 10 ≤ 10 ^ n := by
    calc 10 = 10 ^ 1 := by simp
    _ ≤ 10 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsq : 10 ^ (2 * n) = (10 ^ n) ^ 2 := by ring
  have hfac : 10 ^ (2 * n) - 1 = (10 ^ n - 1) * (10 ^ n + 1) := by
    obtain ⟨c, hc⟩ : ∃ c, 10 ^ n = 1 + c := ⟨10 ^ n - 1, by omega⟩
    rw [hsq, hc]
    have hsq1 : (1 + c) ^ 2 = 1 + (c * c + 2 * c) := by ring
    have hmul : ((1 + c) - 1) * ((1 + c) + 1) = c * c + 2 * c := by
      have e1 : (1 + c) - 1 = c := by omega
      have e2 : (1 + c) + 1 = c + 2 := by omega
      rw [e1, e2]; ring
    omega
  have hdvd : p ∣ (10 ^ n - 1) * (10 ^ n + 1) := hfac ▸ hdiv
  have hplus : p ∣ 10 ^ n + 1 := by
    obtain h | h := (hp.dvd_mul.mp hdvd)
    · exact absurd h hnot
    · exact h
  obtain ⟨t, ht⟩ := hplus
  have hpk : p * ((10 ^ (2 * n) - 1) / p) = 10 ^ (2 * n) - 1 :=
    Nat.mul_div_cancel' hdiv
  have hkey : p * ((10 ^ n - 1) * t) = 10 ^ (2 * n) - 1 := by
    calc p * ((10 ^ n - 1) * t) = (10 ^ n - 1) * (p * t) := by ring
    _ = (10 ^ n - 1) * (10 ^ n + 1) := by rw [← ht]
    _ = 10 ^ (2 * n) - 1 := hfac.symm
  have hk : (10 ^ (2 * n) - 1) / p = (10 ^ n - 1) * t :=
    Nat.mul_left_cancel hp_pos (hkey.trans hpk.symm) |>.symm
  have ht_ne : t ≠ 0 := by
    intro h0
    rw [h0, Nat.mul_zero] at ht
    omega
  have ht_pos : 0 < t := Nat.pos_of_ne_zero ht_ne
  have h2t : 2 * t ≤ 10 ^ n + 1 := by
    calc 2 * t ≤ p * t := by gcongr
    _ = 10 ^ n + 1 := ht.symm
  have htle : t ≤ 10 ^ n := by omega
  have ht_lt : t < 10 ^ n := by omega
  obtain ⟨s, hs⟩ : ∃ s, 10 ^ n = t + s := Nat.exists_eq_add_of_le htle
  obtain ⟨r, hr⟩ : ∃ r, t = r + 1 := ⟨t - 1, by omega⟩
  subst hr
  have hs_eq : 10 ^ n - (r + 1) = s := by omega
  have hr_eq : (r + 1) - 1 = r := by omega
  have hA : 10 ^ n - 1 = s + r := by omega
  have hk_eq : (10 ^ (2 * n) - 1) / p = s + 10 ^ n * r := by
    rw [hk, hA, hs]
    ring
  have hApos : 0 < 10 ^ n := by omega
  have hs_lt : s < 10 ^ n := by omega
  have hmod : ((10 ^ (2 * n) - 1) / p) % 10 ^ n = s := by
    rw [hk_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs_lt]
  have hdiv2 : ((10 ^ (2 * n) - 1) / p) / 10 ^ n = r := by
    rw [hk_eq, Nat.add_mul_div_left _ _ hApos, Nat.div_eq_of_lt hs_lt,
      Nat.zero_add]
  have e1 : Nat.ofDigits 10 (List.take n (Nat.digits 10 ((10 ^ (2 * n) - 1) / p))) =
    ((10 ^ (2 * n) - 1) / p) % 10 ^ n :=
    (Nat.self_mod_pow_eq_ofDigits_take n _ (by norm_num)).symm
  have e2 : Nat.ofDigits 10 (List.drop n (Nat.digits 10 ((10 ^ (2 * n) - 1) / p))) =
    ((10 ^ (2 * n) - 1) / p) / 10 ^ n :=
    (Nat.self_div_pow_eq_ofDigits_drop n _ (by norm_num)).symm
  rw [e1, e2, hmod, hdiv2]
  omega
set_option linter.unusedVariables false in

end MetaMathlibExt

namespace MetaMathlibExt

/--
[midy_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Digits/Midy.lean)
-/
@[path]
lemma midy_theorem
  {p n : ℕ}
-- given
  (hp : Nat.Prime p)
  (h0 : p ≠ 2)
  (h1 : p ≠ 5)
  (hn : 0 < n)
  (hdiv : p ∣ 10 ^ (2 * n) - 1)
  (hmin : ∀ m : ℕ, 0 < m → m < 2 * n → ¬p ∣ 10 ^ m - 1) :
-- imply
  Nat.ofDigits 10 (List.take n (Nat.digits 10 ((10 ^ (2 * n) - 1) / p))) +
    Nat.ofDigits 10 (List.drop n (Nat.digits 10 ((10 ^ (2 * n) - 1) / p))) =
    10 ^ n - 1 := by
-- proof
  exact midy_theorem_general hp hdiv (hmin n hn (by omega))

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
