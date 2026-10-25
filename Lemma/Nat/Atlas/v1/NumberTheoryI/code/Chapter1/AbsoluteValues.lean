import Mathlib
import sympy.Basic
import Def.v1.Atlas.NumberTheoryI.code.Chapter1.AbsoluteValues.Part2
open Finset in
open scoped BigOperators


/--
[ostrowski_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter1/AbsoluteValues.lean)
-/
@[path]
lemma ostrowski_theorem
  {v : AbsoluteValue ℚ ℝ}
-- given
  (hv : v.IsNontrivial) :
-- imply
  v.IsEquiv absAbsoluteValue ∨ (∃ p : ℕ, ∃ (_ : Fact (Nat.Prime p)), v.IsEquiv (padicAbsoluteValueReal p)) := by
-- proof
  obtain h | ⟨p, ⟨hp, h⟩, _⟩ := Rat.AbsoluteValue.equiv_real_or_padic v hv
  · exact Or.inl h
  · exact Or.inr ⟨p, hp, h⟩
open scoped BigOperators

/--
[padicNorm_eq_one_of_not_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter1/AbsoluteValues.lean)
-/
@[path]
lemma padicNorm_eq_one_of_not_dvd
  {x : ℚ}
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
-- given
  (hnum : ¬ p ∣ x.num.natAbs)
  (hden : ¬ p ∣ x.den) :
-- imply
  padicNorm p x = 1 := by
-- proof
  rw [show (x : ℚ) = x.num / x.den from (Rat.num_div_den x).symm, padicNorm.div,
    (padicNorm.int_eq_one_iff _).mpr (by rwa [Int.ofNat_dvd_left]),
    (padicNorm.nat_eq_one_iff _).mpr hden, div_one]

/--
[finite_nat_primes_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter1/AbsoluteValues.lean)
-/
@[path]
lemma finite_nat_primes_dvd
  {N : ℕ}
-- given
  (hN : N ≠ 0) :
-- imply
  {p : Nat.Primes | (p : ℕ) ∣ N}.Finite :=
-- proof
  (((Finset.Icc 1 N : Finset ℕ).preimage (fun p : Nat.Primes => (p : ℕ))
    (fun a _ b _ h => Subtype.val_injective h)).finite_toSet).subset fun ⟨p, hp⟩ hdvd => by
    simp only [Set.mem_setOf_eq] at hdvd
    exact Finset.mem_preimage.mpr (Finset.mem_Icc.mpr
      ⟨hp.one_le, Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hdvd⟩)

/--
[PF_finsupp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter1/AbsoluteValues.lean)
-/
@[path]
lemma PF_finsupp
  {x : ℚ}
-- given
  (hx : x ≠ 0) :
-- imply
  (Function.mulSupport fun p : Nat.Primes => (padicNorm p x : ℝ)).Finite := by
-- proof
  apply (finite_nat_primes_dvd (x.num.natAbs * x.den) (by
    intro heq; rw [Nat.mul_eq_zero] at heq; rcases heq with h | h
    · exact hx (Rat.num_eq_zero.mp (Int.natAbs_eq_zero.mp h))
    · exact absurd h x.den_pos.ne')).subset
  intro ⟨p, hp⟩ hmem
  simp only [Function.mem_mulSupport, Set.mem_setOf_eq] at hmem ⊢
  by_contra hndvd; apply hmem
  exact_mod_cast @padicNorm_eq_one_of_not_dvd x p ⟨hp⟩
    (fun h => hndvd (h.mul_right _)) (fun h => hndvd (h.mul_left _))

/--
[PF_prime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter1/AbsoluteValues.lean)
-/
@[path]
lemma PF_prime
  {q : ℕ}
-- given
  (hq : Nat.Prime q) :
-- imply
  |(↑(q : ℚ) : ℝ)| * ∏ᶠ (p : Nat.Primes), (↑(padicNorm p (q : ℚ)) : ℝ) = 1 := by
-- proof
  have hq_pos : (0 : ℝ) < q := Nat.cast_pos.mpr hq.pos
  rw [show |(↑(q : ℚ) : ℝ)| = (q : ℝ) from by
    rw [show ((q : ℚ) : ℝ) = (q : ℝ) from by push_cast; ring]; exact abs_of_pos hq_pos,
    finprod_eq_single _ ⟨q, hq⟩ (fun ⟨p, hp⟩ hne => by
      simp only; exact_mod_cast @padicNorm.padicNorm_of_prime_of_ne p q ⟨hp⟩ ⟨hq⟩
        (fun h => hne (Subtype.ext h)))]
  push_cast [padicNorm.padicNorm_p hq.one_lt]
  exact mul_inv_cancel₀ hq_pos.ne'

/--
[PF_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter1/AbsoluteValues.lean)
-/
@[path]
lemma PF_mul
  {a b : ℚ}
-- given
  (hfa : (Function.mulSupport fun p : Nat.Primes => (padicNorm p a : ℝ)).Finite)
  (hfb : (Function.mulSupport fun p : Nat.Primes => (padicNorm p b : ℝ)).Finite)
  (ha1 : |(a : ℝ)| * ∏ᶠ (p : Nat.Primes), (↑(padicNorm p a) : ℝ) = 1)
  (hb1 : |(b : ℝ)| * ∏ᶠ (p : Nat.Primes), (↑(padicNorm p b) : ℝ) = 1) :
-- imply
  |(↑(a * b) : ℝ)| * ∏ᶠ (p : Nat.Primes), (↑(padicNorm p (a * b)) : ℝ) = 1 := by
-- proof
  have hprod_eq : (fun p : Nat.Primes => (padicNorm p (a * b) : ℝ)) =
    (fun p : Nat.Primes => (padicNorm p a : ℝ) * (padicNorm p b : ℝ)) := by
    ext ⟨p, hp⟩; simp only; exact_mod_cast @padicNorm.mul p ⟨hp⟩ a b
  rw [show |(↑(a * b) : ℝ)| = |(a : ℝ)| * |(b : ℝ)| from by push_cast; exact abs_mul _ _,
    hprod_eq, finprod_mul_distrib hfa hfb,
    show |(a : ℝ)| * |(b : ℝ)| * ((∏ᶠ p : Nat.Primes, (↑(padicNorm p a) : ℝ)) *
      (∏ᶠ p : Nat.Primes, (↑(padicNorm p b) : ℝ))) =
      (|(a : ℝ)| * ∏ᶠ p : Nat.Primes, (↑(padicNorm p a) : ℝ)) *
      (|(b : ℝ)| * ∏ᶠ p : Nat.Primes, (↑(padicNorm p b) : ℝ)) from by ring,
    ha1, hb1, mul_one]

/--
[PF_nat_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter1/AbsoluteValues.lean)
-/
@[path]
lemma PF_nat_pos
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  |(↑(n : ℚ) : ℝ)| * ∏ᶠ (p : Nat.Primes), (↑(padicNorm p (n : ℚ)) : ℝ) = 1 := by
-- proof
  induction n using Nat.strongRecOn with
  | _ n ih =>
  by_cases hn1 : n = 1
  · subst hn1; simp
  · set q := n.minFac; set m := n / q
    have hq_prime := Nat.minFac_prime (by omega)
    have hmq : m * q = n := Nat.div_mul_cancel (Nat.minFac_dvd n)
    have hm_pos : 0 < m := Nat.div_pos (Nat.le_of_dvd hn (Nat.minFac_dvd n)) hq_prime.pos
    have hm_lt : m < n := Nat.div_lt_self hn hq_prime.one_lt
    rw [show (n : ℚ) = (m : ℚ) * (q : ℚ) from by exact_mod_cast hmq.symm]
    exact PF_mul _ _
      (PF_finsupp _ (Nat.cast_ne_zero.mpr hm_pos.ne'))
      (PF_finsupp _ (Nat.cast_ne_zero.mpr hq_prime.pos.ne'))
      (ih m hm_lt hm_pos) (PF_prime q hq_prime)

/--
[PF_int](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter1/AbsoluteValues.lean)
-/
@[path]
lemma PF_int
  {z : ℤ}
-- given
  (hz : z ≠ 0) :
-- imply
  |(↑(z : ℚ) : ℝ)| * ∏ᶠ (p : Nat.Primes), (↑(padicNorm p (z : ℚ)) : ℝ) = 1 := by
-- proof
  have hna : 0 < z.natAbs := Int.natAbs_pos.mpr hz
  obtain hz_neg | hz_pos := Int.lt_or_lt_of_ne hz
  · have heq : (z : ℚ) = -((z.natAbs : ℕ) : ℚ) := by
    rw [← Int.cast_natCast z.natAbs, ← Int.cast_neg]; congr 1; omega
    simp_rw [heq, padicNorm.neg, show |((-↑↑z.natAbs : ℚ) : ℝ)| = |(↑(↑z.natAbs : ℚ) : ℝ)| from by
      push_cast; exact abs_neg _]
    exact PF_nat_pos z.natAbs hna
  · have heq : (z : ℚ) = ((z.natAbs : ℕ) : ℚ) := by
    rw [← Int.cast_natCast z.natAbs]; congr 1
    exact (Int.natAbs_of_nonneg hz_pos.le).symm
    rw [heq]; exact PF_nat_pos z.natAbs hna

/--
[product_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter1/AbsoluteValues.lean)
-/
@[path]
lemma product_formula
  {x : ℚ}
-- given
  (hx : x ≠ 0) :
-- imply
  |(x : ℝ)| * ∏ᶠ (p : Nat.Primes), (↑(padicNorm p x) : ℝ) = 1 := by
-- proof
  have hx_eq : x = (x.num : ℚ) / (x.den : ℚ) := by
    rw [← Int.cast_natCast x.den]; exact (Rat.num_div_den x).symm
  rw [hx_eq,
    show |(↑((x.num : ℚ) / (x.den : ℚ)) : ℝ)| = |(↑(x.num : ℚ) : ℝ)| / |(↑(x.den : ℚ) : ℝ)| from by
      push_cast; exact abs_div _ _]
  rw [show (fun p : Nat.Primes => (padicNorm p ((x.num : ℚ) / (x.den : ℚ)) : ℝ)) =
    (fun p : Nat.Primes => (padicNorm p (x.num : ℚ) : ℝ) / (padicNorm p (x.den : ℚ) : ℝ)) from by
    ext ⟨p, hp⟩; simp only; exact_mod_cast @padicNorm.div p ⟨hp⟩ (x.num : ℚ) (x.den : ℚ)]
  rw [finprod_div_distrib
    (PF_finsupp _ (Int.cast_ne_zero.mpr (Rat.num_ne_zero.mpr hx)))
    (PF_finsupp _ (Nat.cast_ne_zero.mpr x.den_pos.ne')),
    div_mul_div_comm,
    PF_int x.num (Rat.num_ne_zero.mpr hx),
    PF_nat_pos x.den x.den_pos,
    div_self one_ne_zero]

/--
[AbsoluteValue.pow_le_mul_max_pow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter1/AbsoluteValues.lean)
-/
@[path]
lemma AbsoluteValue.pow_le_mul_max_pow
  [Field k]
  {v : AbsoluteValue k ℝ}
  {x y : k}
  {n : ℕ}
-- given
  (hv : ∀ n : ℕ, v (↑n) ≤ 1) :
-- imply
  v (x + y) ^ n ≤ (↑n + 1) * (max (v x) (v y)) ^ n := by
-- proof
  rw [← v.map_pow]
  rw [add_pow x y n]
  calc v (∑ m ∈ range (n + 1), x ^ m * y ^ (n - m) * ↑(n.choose m))
    ≤ ∑ m ∈ range (n + 1), v (x ^ m * y ^ (n - m) * ↑(n.choose m)) :=
      v.sum_le _ _
    _ ≤ ∑ _m ∈ range (n + 1), (max (v x) (v y)) ^ n := by
      apply sum_le_sum
      intro m hm
      rw [mem_range] at hm
      have hmn : m + (n - m) = n := Nat.add_sub_cancel' (by omega)
      calc v (x ^ m * y ^ (n - m) * ↑(n.choose m))
        = v x ^ m * v y ^ (n - m) * v (↑(n.choose m)) := by
          rw [map_mul, map_mul, map_pow, map_pow]
        _ ≤ v x ^ m * v y ^ (n - m) * 1 :=
          mul_le_mul_of_nonneg_left (hv _)
            (mul_nonneg (pow_nonneg (v.nonneg _) _) (pow_nonneg (v.nonneg _) _))
        _ = v x ^ m * v y ^ (n - m) := by ring
        _ ≤ (max (v x) (v y)) ^ m * (max (v x) (v y)) ^ (n - m) :=
          mul_le_mul
            (pow_le_pow_left₀ (v.nonneg _) (le_max_left _ _) _)
            (pow_le_pow_left₀ (v.nonneg _) (le_max_right _ _) _)
            (pow_nonneg (v.nonneg _) _)
            (pow_nonneg (le_max_of_le_left (v.nonneg _)) _)
        _ = (max (v x) (v y)) ^ n := by rw [← pow_add, hmn]
    _ = (↑n + 1) * (max (v x) (v y)) ^ n := by
      simp [sum_const, card_range]

/--
[AbsoluteValue.isNonarchimedean_iff_natCast_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter1/AbsoluteValues.lean)
-/
@[path]
lemma AbsoluteValue.isNonarchimedean_iff_natCast_le_one
  [Field k]
  {v : AbsoluteValue k ℝ} :
-- imply
  IsNonarchimedean (v : k → ℝ) ↔ ∀ n : ℕ, 0 < n → v (n • (1 : k)) ≤ 1 := by
-- proof
  constructor
  ·
    intro hna n _hn
    rw [nsmul_eq_mul, mul_one]
    exact IsNonarchimedean.apply_natCast_le_one_of_isNonarchimedean hna
  ·
    intro hv x y
    have hv' : ∀ n : ℕ, v (↑n) ≤ 1 := by
      intro n
      obtain rfl | hn := n.eq_zero_or_pos
      · simp [v.map_zero]
      · specialize hv n hn
        rwa [nsmul_eq_mul, mul_one] at hv
    by_contra hlt
    push Not at hlt
    have hM_pos : 0 < max (v x) (v y) := by
      by_contra h
      push Not at h
      have hx : v x = 0 := le_antisymm ((le_max_left _ _).trans h) (v.nonneg x)
      have hy : v y = 0 := le_antisymm ((le_max_right _ _).trans h) (v.nonneg y)
      simp [v.eq_zero.mp hx, v.eq_zero.mp hy] at hlt
    set M := max (v x) (v y)
    set r := v (x + y) / M
    have hr_gt_one : 1 < r := (one_lt_div hM_pos).mpr hlt
    have hr_bound : ∀ n : ℕ, r ^ n ≤ ↑n + 1 := by
      intro n
      rw [div_pow, div_le_iff₀ (pow_pos hM_pos n)]
      exact v.pow_le_mul_max_pow hv' x y n
    obtain ⟨m, hm⟩ := Real.exists_natCast_add_one_lt_pow_of_one_lt hr_gt_one
    linarith [hr_bound m]

/--
[lemma_1_4_forward](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter1/AbsoluteValues.lean)
-/
@[path]
lemma lemma_1_4_forward
  [Field k]
  {v : AbsoluteValue k ℝ}
-- given
  (hv : IsNonarchimedean v) :
-- imply
  ∀ n : ℕ, v (n : k) ≤ 1 :=
-- proof
  fun _ => hv.apply_natCast_le_one_of_isNonarchimedean

/--
[lemma_1_4](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter1/AbsoluteValues.lean)
-/
@[path]
lemma lemma_1_4
  [Field k]
  {v : AbsoluteValue k ℝ} :
-- imply
  IsNonarchimedean v ↔ ∀ n : ℕ, v (n : k) ≤ 1 :=
-- proof
  ⟨lemma_1_4_forward v,
    fun hv => (v.isNonarchimedean_iff_natCast_le_one).mpr
      (fun n _ => by rw [nsmul_eq_mul, mul_one]; exact hv n)⟩
section Corollary_1_5

/--
[corollary_1_5_part1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter1/AbsoluteValues.lean)
-/
@[path]
lemma corollary_1_5_part1
  [Field k]
  {p : ℕ}
  [CharP k p]
  {v : AbsoluteValue k ℝ}
-- given
  (hp : p ≠ 0) :
-- imply
  IsNonarchimedean v := by
-- proof
  apply (lemma_1_4 v).mpr
  intro n
  by_cases hdvd : p ∣ n
  ·
    rw [show (n : k) = 0 from (CharP.cast_eq_zero_iff k p n).mpr hdvd, map_zero]
    exact le_of_lt one_pos
  ·
    have hn : (n : k) ≠ 0 := by rwa [Ne, CharP.cast_eq_zero_iff k p]
    haveI : NeZero p := ⟨hp⟩
    haveI hp' : Fact (Nat.Prime p) := CharP.char_is_prime_of_pos k p
    haveI : ExpChar k p := ExpChar.prime hp'.out
    have hfrob : (n : k) ^ p = (n : k) := by
      rw [← frobenius_def]; exact map_natCast (frobenius k p) n
    have hpow : (n : k) ^ (p - 1) = 1 := by
      have hp1 : 1 ≤ p := Nat.Prime.one_le hp'.out
      have : (n : k) ^ (p - 1) * (n : k) = 1 * (n : k) := by
        rwa [one_mul, ← pow_succ, Nat.sub_add_cancel hp1]
      exact mul_right_cancel₀ hn this
    have hvpow : v (n : k) ^ (p - 1) = 1 := by
      rw [← map_pow, hpow, map_one]
    have hp1ne : (p - 1 : ℕ) ≠ 0 := by
      have := Nat.Prime.two_le hp'.out; omega
    exact le_of_eq ((pow_eq_one_iff_of_nonneg (v.nonneg _) hp1ne).mp hvpow)

/--
[corollary_1_5_part2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter1/AbsoluteValues.lean)
-/
@[path]
lemma corollary_1_5_part2
  [Field k]
  [Fintype k]
  {v : AbsoluteValue k ℝ} :
-- imply
  ∀ x : k, x ≠ 0 → v x = 1 := by
-- proof
  intro x hx
  have hpow : x ^ (Fintype.card k - 1) = 1 := FiniteField.pow_card_sub_one_eq_one x hx
  have hvpow : v x ^ (Fintype.card k - 1) = 1 := by
    rw [← map_pow, hpow, map_one]
  have hcard : Fintype.card k - 1 ≠ 0 := by
    have := Fintype.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial k)
    omega
  exact (pow_eq_one_iff_of_nonneg (v.nonneg _) hcard).mp hvpow

/--
[absValue_charP_isNonarchimedean_and_finite_trivial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter1/AbsoluteValues.lean)
-/
@[path]
lemma absValue_charP_isNonarchimedean_and_finite_trivial
  [Field k]
  {v : AbsoluteValue k ℝ}
  {p : ℕ}
  [CharP k p]
-- given
  (hp : p ≠ 0) :
-- imply
  IsNonarchimedean v ∧ (∀ [Fintype k], ∀ x : k, x ≠ 0 → v x = 1) :=
-- proof
  ⟨corollary_1_5_part1 hp v, fun {_} x hx => corollary_1_5_part2 v x hx⟩
end Corollary_1_5


-- created on 2026-10-23
