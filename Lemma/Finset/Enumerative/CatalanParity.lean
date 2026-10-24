import Mathlib
import sympy.Basic


namespace MetaMathlibExt

/--
[digits_two_two_mul_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CatalanParity.lean)
-/
@[path]
private lemma digits_two_two_mul_sum (n : ℕ) :
  (Nat.digits 2 (2 * n)).sum = (Nat.digits 2 n).sum := by
  obtain rfl | hpos := Nat.eq_zero_or_pos n
  · simp
  · rw [Nat.digits_base_mul (by norm_num) hpos, List.sum_cons, Nat.zero_add]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[padicValNat_centralBinom_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CatalanParity.lean)
-/
@[path]
private lemma padicValNat_centralBinom_two (n : ℕ) :
  padicValNat 2 n.centralBinom = (Nat.digits 2 n).sum := by
  have _hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.centralBinom_eq_two_mul_choose]
  have hle : n ≤ 2 * n := Nat.le_mul_of_pos_left n (by norm_num)
  have h := sub_one_mul_padicValNat_choose_eq_sub_sum_digits (p := 2) (k := n) (n := 2 * n) hle
  simp only [show (2 : ℕ) - 1 = 1 from rfl, one_mul] at h
  have hsub : 2 * n - n = n := by omega
  rw [hsub] at h
  have h2n : (Nat.digits 2 (2 * n)).sum = (Nat.digits 2 n).sum :=
    digits_two_two_mul_sum n
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[catalan_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CatalanParity.lean)
-/
@[path]
private lemma catalan_ne_zero (n : ℕ) : catalan n ≠ 0 := by
  have h := succ_mul_catalan_eq_centralBinom n
  have hpos : 0 < n.centralBinom := Nat.centralBinom_pos n
  intro hz
  rw [hz, mul_zero] at h
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[padicValNat_catalan_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CatalanParity.lean)
-/
@[path]
private lemma padicValNat_catalan_add (n : ℕ) :
  padicValNat 2 (n + 1) + padicValNat 2 (catalan n) = (Nat.digits 2 n).sum := by
  have _hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := succ_mul_catalan_eq_centralBinom n
  have h1 : (n : ℕ) + 1 ≠ 0 := by omega
  have h2 : catalan n ≠ 0 := catalan_ne_zero n
  have hmul := padicValNat.mul (p := 2) (a := n + 1) (b := catalan n) h1 h2
  rwa [h, padicValNat_centralBinom_two n] at hmul

end MetaMathlibExt

namespace MetaMathlibExt

/--
[odd_iff_padicValNat_two_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CatalanParity.lean)
-/
@[path]
private lemma odd_iff_padicValNat_two_eq_zero (m : ℕ) (hm : m ≠ 0) :
  Odd m ↔ padicValNat 2 m = 0 := by
  have _hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · intro hod
    apply padicValNat.eq_zero_of_not_dvd
    intro hdvd
    obtain ⟨k, hk⟩ := hod
    obtain ⟨j, hj⟩ := hdvd
    omega
  · intro h0
    rw [← Nat.not_even_iff_odd]
    intro hev
    rw [even_iff_two_dvd] at hev
    have h1 := one_le_padicValNat_of_dvd hm hev
    omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[digits_two_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CatalanParity.lean)
-/
@[path]
private lemma digits_two_sum_le (n : ℕ) : (Nat.digits 2 n).sum ≤ n := by
  have h1 : (1 : ℕ) ≤ 2 := by norm_num
  calc (Nat.digits 2 n).sum ≤ Nat.ofDigits 2 (Nat.digits 2 n) :=
    Nat.sum_le_ofDigits (Nat.digits 2 n) h1
    _ = n := Nat.ofDigits_digits 2 n

end MetaMathlibExt

namespace MetaMathlibExt

/--
[digits_two_succ_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CatalanParity.lean)
-/
@[path]
private lemma digits_two_succ_add (n : ℕ) :
  (Nat.digits 2 n).sum + 1
    = (Nat.digits 2 (n + 1)).sum + padicValNat 2 (n + 1) := by
  have _hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := sub_one_mul_padicValNat_factorial (p := 2) n
  have h2 := sub_one_mul_padicValNat_factorial (p := 2) (n + 1)
  simp only [show (2 : ℕ) - 1 = 1 from rfl, one_mul] at h1 h2
  have hfact : (n + 1).factorial = (n + 1) * n.factorial := Nat.factorial_succ n
  have hne1 : (n : ℕ) + 1 ≠ 0 := by omega
  have hneF : n.factorial ≠ 0 := Nat.factorial_ne_zero n
  have hmul := padicValNat.mul (p := 2) (a := n + 1) (b := n.factorial) hne1 hneF
  rw [← hfact] at hmul
  have hs1 := digits_two_sum_le n
  have hs2 := digits_two_sum_le (n + 1)
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ofDigits_two_eq_zero_of_sum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CatalanParity.lean)
-/
@[path]
private lemma ofDigits_two_eq_zero_of_sum_eq_zero (L : List ℕ) (hsum : L.sum = 0) :
  Nat.ofDigits 2 L = 0 := by
  induction L with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.sum_cons] at hsum
    have hd0 : hd = 0 := by omega
    have htl : tl.sum = 0 := by omega
    rw [Nat.ofDigits_cons, hd0, ih htl, Nat.zero_add, mul_zero]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ofDigits_two_sum_eq_one_aux](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CatalanParity.lean)
-/
@[path]
private lemma ofDigits_two_sum_eq_one_aux (L : List ℕ) :
  (∀ d ∈ L, d < 2) → L.sum = 1 → ∃ k, Nat.ofDigits 2 L = 2 ^ k := by
  induction L with
  | nil => intro _ hsum; simp at hsum
  | cons hd tl ih =>
    intro hall hsum
    simp only [List.sum_cons] at hsum
    have hdlt : hd < 2 := hall hd (by simp)
    have hall_tl : ∀ d ∈ tl, d < 2 := fun d hd' => hall d (List.mem_cons_of_mem hd hd')
    have h01 : hd = 0 ∨ hd = 1 := by omega
    obtain rfl | rfl := h01
    · have hsum_tl : tl.sum = 1 := by omega
      obtain ⟨k, hk⟩ := ih hall_tl hsum_tl
      exact ⟨k + 1, by rw [Nat.ofDigits_cons, hk]; ring⟩
    · have hsum_tl : tl.sum = 0 := by omega
      have h0 := ofDigits_two_eq_zero_of_sum_eq_zero tl hsum_tl
      exact ⟨0, by rw [Nat.ofDigits_cons, h0]; simp⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[digits_two_sum_eq_one_of_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CatalanParity.lean)
-/
@[path]
private lemma digits_two_sum_eq_one_of_pow (a : ℕ) :
  (Nat.digits 2 (2 ^ a)).sum = 1 := by
  have h1 : (1 : ℕ) < 2 := by norm_num
  have h2 : (0 : ℕ) < 1 := by norm_num
  have hdig1 : Nat.digits 2 1 = [1] := Nat.digits_of_lt 2 1 (by norm_num) (by norm_num)
  have hdig : Nat.digits 2 (2 ^ a) = List.replicate a 0 ++ [1] := by
    have hbase := Nat.digits_base_pow_mul (b := 2) (k := a) (m := 1) h1 h2
    simp only [mul_one] at hbase
    rw [hbase, hdig1]
  rw [hdig, List.sum_append]
  simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pow_two_of_digits_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CatalanParity.lean)
-/
@[path]
private lemma pow_two_of_digits_sum_eq_one (m : ℕ) (_hm : m ≠ 0)
  (hsum : (Nat.digits 2 m).sum = 1) : ∃ a, m = 2 ^ a := by
  have hall : ∀ d ∈ Nat.digits 2 m, d < 2 :=
    fun d hd => Nat.digits_lt_base (by norm_num) hd
  obtain ⟨k, hk⟩ := ofDigits_two_sum_eq_one_aux (Nat.digits 2 m) hall hsum
  rw [Nat.ofDigits_digits] at hk
  exact ⟨k, hk⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[catalan_odd_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CatalanParity.lean)
-/
@[path]
lemma catalan_odd_iff
  {n : ℕ} :
-- imply
  Odd (catalan n) ↔ ∃ a : ℕ, n = 2 ^ a - 1 := by
-- proof
  have _hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hadd := padicValNat_catalan_add n
  have hsucc := digits_two_succ_add n
  have hcat := catalan_ne_zero n
  rw [odd_iff_padicValNat_two_eq_zero _ hcat]
  constructor
  · intro h0
    have hvn : padicValNat 2 (n + 1) = (Nat.digits 2 n).sum := by omega
    have hs1 : (Nat.digits 2 (n + 1)).sum = 1 := by omega
    obtain ⟨a, ha⟩ := pow_two_of_digits_sum_eq_one (n + 1) (by omega) hs1
    exact ⟨a, by omega⟩
  · rintro ⟨a, rfl⟩
    have hpos : 0 < 2 ^ a := Nat.pow_pos (by norm_num)
    have hsucc_eq : 2 ^ a - 1 + 1 = 2 ^ a := by omega
    have hs1 : (Nat.digits 2 (2 ^ a)).sum = 1 := digits_two_sum_eq_one_of_pow a
    rw [hsucc_eq] at hadd hsucc
    rw [hs1] at hsucc
    omega
end



-- created on 2026-10-20
-- updated on 2026-10-23
