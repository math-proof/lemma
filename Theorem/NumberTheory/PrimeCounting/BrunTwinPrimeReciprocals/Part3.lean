/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/BrunTwinPrimeReciprocals.lean -/

import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Def.NumberTheory.SelbergSieve
import Lemma.Nat.SelbergSieve
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Def.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocals.Part3
/-!
# Brun's theorem on twin-prime reciprocals

This file records the convergence of the reciprocal series over twin-prime pairs.
-/


section

namespace MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

open MathlibExt.SelbergSieve

-- N3 (proved)
theorem brunRho_one : brunRho 1 = 1 := by decide

theorem brunRho_odd_prime (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : brunRho p = 2 := by
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    omega
  have hsub : p - 2 < p := by omega
  have hne : (0 : ℕ) ≠ p - 2 := by omega
  unfold brunRho
  have hset : (Finset.range p).filter (fun a => p ∣ a * (a + 2)) = {0, p - 2} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨halt, hdvd⟩
      rcases (hp.dvd_mul.mp hdvd) with h | h
      · have haz : a = 0 := by
          by_contra hne2
          have hpos : 0 < a := Nat.pos_of_ne_zero hne2
          have hle : p ≤ a := Nat.le_of_dvd hpos h
          omega
        exact Or.inl haz
      · have hpos2 : 0 < a + 2 := by omega
        have hle : p ≤ a + 2 := Nat.le_of_dvd hpos2 h
        have hub : a + 2 ≤ p + 1 := by omega
        have hap : a + 2 = p := by
          by_contra hne2
          have h1 : p ∣ p + 1 := by
            have htmp : a + 2 = p + 1 := by omega
            rw [← htmp]; exact h
          have hdvd1 : p ∣ 1 := (Nat.dvd_add_right (dvd_refl p)).mp h1
          have hle1 := Nat.le_of_dvd (by norm_num) hdvd1
          omega
        exact Or.inr (by omega)
    · rintro (rfl | rfl)
      · exact ⟨hp.pos, by simp⟩
      · refine ⟨hsub, ?_⟩
        have hpp : (p - 2) + 2 = p := by omega
        rw [hpp]
        exact dvd_mul_left p (p - 2)
  rw [hset, Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]

-- N2: multiplicativity of brunRho
theorem brunRho_zero : brunRho 0 = 0 := by
  unfold brunRho
  simp

theorem brunRho_mul_of_coprime (m n : ℕ) (h : m.Coprime n) :
    brunRho (m * n) = brunRho m * brunRho n := by
  by_cases hm0 : m = 0
  · subst hm0
    have hn1 : n = 1 := (Nat.coprime_zero_left n).mp h
    subst hn1
    simp [brunRho_zero, brunRho_one]
  by_cases hn0 : n = 0
  · subst hn0
    have hm1 : m = 1 := (Nat.coprime_zero_left m).mp h.symm
    subst hm1
    simp [brunRho_zero, brunRho_one]
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  -- Transfer of the divisibility predicate to residues.
  have htrans : ∀ (a d : ℕ), d ∣ a * (a + 2) ↔ d ∣ (a % d) * ((a % d) + 2) := by
    intro a d
    by_cases hd0 : d = 0
    · subst hd0
      simp [Nat.mod_zero]
    have h1 : a ≡ a % d [MOD d] := (Nat.mod_modEq a d).symm
    have h2 : a + 2 ≡ (a % d) + 2 [MOD d] := Nat.ModEq.add_right 2 h1
    have hmul : a * (a + 2) ≡ (a % d) * ((a % d) + 2) [MOD d] :=
      Nat.ModEq.mul h1 h2
    exact Nat.ModEq.dvd_iff hmul (dvd_refl d)
  have htrans' : ∀ (k b d : ℕ), k ≡ b [MOD d] →
      (d ∣ k * (k + 2) ↔ d ∣ b * (b + 2)) := by
    intro k b d hmod
    have h2 : k + 2 ≡ b + 2 [MOD d] := Nat.ModEq.add_right 2 hmod
    have hmul : k * (k + 2) ≡ b * (b + 2) [MOD d] :=
      Nat.ModEq.mul hmod h2
    exact Nat.ModEq.dvd_iff hmul (dvd_refl d)
  have hmul_dvd : ∀ x : ℕ, m * n ∣ x ↔ m ∣ x ∧ n ∣ x := by
    intro x
    constructor
    · intro hdiv
      exact ⟨dvd_trans (dvd_mul_right m n) hdiv,
        dvd_trans (dvd_mul_left n m) hdiv⟩
    · rintro ⟨h1, h2⟩
      exact h.mul_dvd_of_dvd_of_dvd h1 h2
  -- The two finite sets.
  set S : Finset ℕ :=
    (Finset.range (m * n)).filter (fun a => m * n ∣ a * (a + 2)) with hS
  set T : Finset (ℕ × ℕ) :=
    ((Finset.range m) ×ˢ (Finset.range n)).filter
      (fun bc => m ∣ bc.1 * (bc.1 + 2) ∧ n ∣ bc.2 * (bc.2 + 2)) with hT
  have hST : S.card = T.card := by
    apply Finset.card_nbij' (fun a => (a % m, a % n))
      (fun bc => ↑(Nat.chineseRemainder h.symm bc.2 bc.1))
    · intro a ha
      simp only [hS, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_range] at ha
      obtain ⟨halt, hdvd⟩ := ha
      have hm_dvd : m ∣ a * (a + 2) :=
        dvd_trans (dvd_mul_right m n) hdvd
      have hn_dvd : n ∣ a * (a + 2) :=
        dvd_trans (dvd_mul_left n m) hdvd
      simp only [hT, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_product, Finset.mem_range]
      refine ⟨⟨Nat.mod_lt a hmpos, Nat.mod_lt a hnpos⟩, ?_, ?_⟩
      · have hiff := (htrans a m).mp hm_dvd
        simpa using hiff
      · have hiff := (htrans a n).mp hn_dvd
        simpa using hiff
    · intro bc hbc
      simp only [hT, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_product, Finset.mem_range] at hbc
      obtain ⟨⟨hb_lt, hc_lt⟩, hb_dvd, hc_dvd⟩ := hbc
      have hlt : (↑(Nat.chineseRemainder h.symm bc.2 bc.1) : ℕ) < n * m :=
        Nat.chineseRemainder_lt_mul h.symm bc.2 bc.1 hn0 hm0
      rw [mul_comm n m] at hlt
      have hprop := (Nat.chineseRemainder h.symm bc.2 bc.1).prop
      obtain ⟨h_n, h_m⟩ := hprop
      -- h_n : k ≡ bc.2 [MOD n], h_m : k ≡ bc.1 [MOD m]
      have hk_m : m ∣ (↑(Nat.chineseRemainder h.symm bc.2 bc.1) : ℕ) *
          (((↑(Nat.chineseRemainder h.symm bc.2 bc.1) : ℕ)) + 2) := by
        have hiff := htrans'
          (↑(Nat.chineseRemainder h.symm bc.2 bc.1) : ℕ) bc.1 m h_m
        exact hiff.mpr hb_dvd
      have hk_n : n ∣ (↑(Nat.chineseRemainder h.symm bc.2 bc.1) : ℕ) *
          (((↑(Nat.chineseRemainder h.symm bc.2 bc.1) : ℕ)) + 2) := by
        have hiff := htrans'
          (↑(Nat.chineseRemainder h.symm bc.2 bc.1) : ℕ) bc.2 n h_n
        exact hiff.mpr hc_dvd
      simp only [hS, Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      exact ⟨hlt, (hmul_dvd _).mpr ⟨hk_m, hk_n⟩⟩
    · intro a ha
      simp only [hS, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_range] at ha
      obtain ⟨halt, -⟩ := ha
      have hlt : (↑(Nat.chineseRemainder h.symm (a % n) (a % m)) : ℕ) < n * m :=
        Nat.chineseRemainder_lt_mul h.symm (a % n) (a % m) hn0 hm0
      rw [mul_comm n m] at hlt
      have hprop := (Nat.chineseRemainder h.symm (a % n) (a % m)).prop
      obtain ⟨h_n, h_m⟩ := hprop
      have ha_m : a ≡ a % m [MOD m] := (Nat.mod_modEq a m).symm
      have ha_n : a ≡ a % n [MOD n] := (Nat.mod_modEq a n).symm
      have hm_eq : (↑(Nat.chineseRemainder h.symm (a % n) (a % m)) : ℕ) ≡
          a [MOD m] := h_m.trans ha_m.symm
      have hn_eq : (↑(Nat.chineseRemainder h.symm (a % n) (a % m)) : ℕ) ≡
          a [MOD n] := h_n.trans ha_n.symm
      have hmn : (↑(Nat.chineseRemainder h.symm (a % n) (a % m)) : ℕ) ≡
          a [MOD m * n] :=
        (Nat.modEq_and_modEq_iff_modEq_mul h).mp ⟨hm_eq, hn_eq⟩
      exact Nat.ModEq.eq_of_lt_of_lt hmn hlt halt
    · intro bc hbc
      simp only [hT, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_product, Finset.mem_range] at hbc
      obtain ⟨⟨hb_lt, hc_lt⟩, -, -⟩ := hbc
      have hprop := (Nat.chineseRemainder h.symm bc.2 bc.1).prop
      obtain ⟨h_n, h_m⟩ := hprop
      have e1 : (↑(Nat.chineseRemainder h.symm bc.2 bc.1) : ℕ) % m = bc.1 := by
        have hmod : (↑(Nat.chineseRemainder h.symm bc.2 bc.1) : ℕ) % m =
            bc.1 % m := h_m
        rw [Nat.mod_eq_of_lt hb_lt] at hmod
        exact hmod
      have e2 : (↑(Nat.chineseRemainder h.symm bc.2 bc.1) : ℕ) % n = bc.2 := by
        have hmod : (↑(Nat.chineseRemainder h.symm bc.2 bc.1) : ℕ) % n =
            bc.2 % n := h_n
        rw [Nat.mod_eq_of_lt hc_lt] at hmod
        exact hmod
      change ((↑(Nat.chineseRemainder h.symm bc.2 bc.1) : ℕ) % m,
        (↑(Nat.chineseRemainder h.symm bc.2 bc.1) : ℕ) % n) = bc
      rw [e1, e2]
  have hTcard : T.card = brunRho m * brunRho n := by
    have hprod : T = (Finset.range m).filter (fun b => m ∣ b * (b + 2)) ×ˢ
        (Finset.range n).filter (fun c => n ∣ c * (c + 2)) := by
      ext ⟨b, c⟩
      simp only [hT, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range]
      constructor
      · rintro ⟨⟨hb, hc⟩, h1, h2⟩
        exact ⟨⟨hb, h1⟩, ⟨hc, h2⟩⟩
      · rintro ⟨⟨hb, h1⟩, ⟨hc, h2⟩⟩
        exact ⟨⟨hb, hc⟩, h1, h2⟩
    rw [hprod, Finset.card_product]
    rfl
  have hScard : S.card = brunRho (m * n) := rfl
  rw [hScard] at hST
  rw [hST, hTcard]

-- N4(a): brunNu is multiplicative
theorem brunNu_one : brunNu 1 = 1 := by
  rw [brunNu_apply, brunRho_one]
  simp

theorem brunNu_mult : brunNu.IsMultiplicative := by
  constructor
  · exact brunNu_one
  · intro m n h
    by_cases hm0 : m = 0
    · subst hm0
      have hn1 : n = 1 := (Nat.coprime_zero_left n).mp h
      subst hn1
      rw [mul_one, brunNu_one, mul_one]
    by_cases hn0 : n = 0
    · subst hn0
      have hm1 : m = 1 := (Nat.coprime_zero_left m).mp h.symm
      subst hm1
      rw [mul_zero, brunNu_one, one_mul]
    have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm0
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
    rw [brunNu_apply, brunNu_apply, brunNu_apply,
      brunRho_mul_of_coprime m n h]
    push_cast
    field_simp

-- N4(b): brunNu at odd prime
theorem brunNu_odd_prime (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) : brunNu p = 2 / (p : ℝ) := by
  rw [brunNu_apply, brunRho_odd_prime p hp hp2]
  norm_cast

-- N4(c): brunP is squarefree
theorem brunP_squarefree (Y : ℕ) : Squarefree (brunP Y) := by
  unfold brunP brunPrimes
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    simp only [Finset.mem_coe, Finset.mem_filter,
      Finset.mem_range] at hp hq
    obtain ⟨-, hpp, -⟩ := hp
    obtain ⟨-, hqp, -⟩ := hq
    have hcop : Nat.Coprime p q :=
      (Nat.coprime_primes hpp hqp).mpr hpq
    exact (Nat.coprime_iff_isRelPrime).mp hcop
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨-, hpp, -⟩ := hp
    exact hpp.prime.squarefree

-- N4(d): prime divisors of brunP
theorem brunP_prime_dvd (Y p : ℕ) (hp : p.Prime) :
    p ∣ brunP Y ↔ (p ≠ 2 ∧ p ≤ Y ^ 2) := by
  have hmem : ∀ q : ℕ, q ∈ brunPrimes Y ↔
      (q < Y ^ 2 + 1 ∧ q.Prime ∧ q ≠ 2) := by
    intro q
    simp [brunPrimes]
  constructor
  · intro hdiv
    have hpp : Prime p := hp.prime
    rw [brunP, Prime.dvd_finsetProd_iff hpp] at hdiv
    obtain ⟨q, hqmem, hpq⟩ := hdiv
    have hq := (hmem q).mp hqmem
    obtain ⟨hq_lt, hq_prime, hq2⟩ := hq
    have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq_prime).mp hpq
    subst heq
    exact ⟨hq2, Nat.lt_succ_iff.mp hq_lt⟩
  · rintro ⟨hp2, hle⟩
    have hqmem : p ∈ brunPrimes Y := by
      rw [hmem]
      exact ⟨Nat.lt_succ_iff.mpr hle, hp, hp2⟩
    unfold brunP
    exact Finset.dvd_prod_of_mem (fun p => p) hqmem

end MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted
end
