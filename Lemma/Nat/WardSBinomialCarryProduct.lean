import Mathlib
import sympy.Basic
import Def.Combinatorics.Enumerative.WardGeneralizedBinomial
import Lemma.Finset.Enumerative.WardGeneralizedBinomial


/--
[card_filter_dvd_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/WardSBinomialCarryProduct.lean)
-/
@[path]
private lemma card_filter_dvd_Icc (b t : Nat) (hb : 0 < b) :
  ((Finset.Icc 1 t).filter (fun i => b ∣ i)).card = t / b := by
  have h1 : ((Finset.Icc 1 t).filter (fun i => b ∣ i)) =
    (Finset.Icc 1 (t / b)).image (fun k => b * k) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · intro h
      obtain ⟨⟨h1x, hxt⟩, hdvd⟩ := h
      obtain ⟨c, hc⟩ := hdvd
      have hcpos : 0 < c := by
        by_contra hcon
        have hc0 : c = 0 := Nat.eq_zero_of_not_pos hcon
        subst hc0
        simp at hc
        omega
      have hbt : b * c ≤ t := by omega
      have hcle : c ≤ t / b := by
        rw [Nat.le_div_iff_mul_le hb]
        calc c * b = b * c := by ring
        _ ≤ t := hbt
      exact ⟨c, ⟨hcpos, hcle⟩, by omega⟩
    · intro h
      obtain ⟨c, ⟨hc1, hc2⟩, rfl⟩ := h
      have hpos : 0 < b * c := Nat.mul_pos hb hc1
      have h11 : b * c ≤ b * (t / b) := Nat.mul_le_mul_left b hc2
      have h2 : b * (t / b) ≤ t := Nat.mul_div_le t b
      have hle : b * c ≤ t := le_trans h11 h2
      exact ⟨⟨hpos, hle⟩, ⟨c, rfl⟩⟩
  rw [h1]
  rw [Finset.card_image_of_injective]
  · rw [Nat.card_Icc, Nat.add_sub_cancel]
  · intro a1 a2 h
    simp only at h
    exact Nat.mul_left_cancel hb h

/--
[divisors_eq_filter_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/WardSBinomialCarryProduct.lean)
-/
@[path]
private lemma divisors_eq_filter_Icc (i t : Nat) (h1i : 1 ≤ i) (hit : i ≤ t) :
  Nat.divisors i = (Finset.Icc 1 t).filter (fun d => d ∣ i) := by
  ext d
  simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · intro h
    obtain ⟨hdvd, hi0⟩ := h
    have hdpos : 0 < d := by
      by_contra hcon
      have hd0 : d = 0 := Nat.eq_zero_of_not_pos hcon
      subst hd0
      simp at hdvd
      omega
    have hdle : d ≤ i := Nat.le_of_dvd (by omega) hdvd
    exact ⟨⟨hdpos, le_trans hdle hit⟩, hdvd⟩
  · intro h
    obtain ⟨⟨_, _⟩, hdvd⟩ := h
    exact ⟨hdvd, by omega⟩

/--
[ffact_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/WardSBinomialCarryProduct.lean)
-/
@[path]
private lemma ffact_eq (s f : Nat → Int)
  (hf : ∀ k, 0 < k → f k = ∏ d ∈ Nat.divisors k, s d) (t : Nat) :
  (∏ i ∈ Finset.Icc 1 t, f i) = ∏ b ∈ Finset.Icc 1 t, s b ^ (t / b) := by
  have step1 : (∏ i ∈ Finset.Icc 1 t, f i)
    = ∏ i ∈ Finset.Icc 1 t, ∏ b ∈ Finset.Icc 1 t, (if b ∣ i then s b else 1) := by
    apply Finset.prod_congr rfl
    intro i hi
    simp only [Finset.mem_Icc] at hi
    rw [hf i (by omega)]
    rw [divisors_eq_filter_Icc i t hi.1 hi.2]
    rw [Finset.prod_filter]
  rw [step1]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro b hb
  simp only [Finset.mem_Icc] at hb
  have hbpos : 0 < b := by omega
  have h2 : (∏ i ∈ Finset.Icc 1 t, (if b ∣ i then s b else 1))
    = ∏ i ∈ (Finset.Icc 1 t).filter (fun i => b ∣ i), s b := by
    rw [Finset.prod_filter]
  rw [h2, Finset.prod_const, card_filter_dvd_Icc b t hbpos]

/--
[carry_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/WardSBinomialCarryProduct.lean)
-/
@[path]
private lemma carry_eq (n m b : Nat) (hb : 0 < b) :
  (n + m) / b = n / b + m / b + (n % b + m % b) / b := by
  have hn : b * (n / b) + n % b = n := Nat.div_add_mod n b
  have hm : b * (m / b) + m % b = m := Nat.div_add_mod m b
  have h : n + m = b * (n / b + m / b) + (n % b + m % b) := by
    calc n + m = (b * (n / b) + n % b) + (b * (m / b) + m % b) := by rw [hn, hm]
    _ = b * (n / b + m / b) + (n % b + m % b) := by ring
  conv_lhs => rw [h]
  rw [Nat.mul_add_div hb]

/--
[ffact_eq_extend](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/WardSBinomialCarryProduct.lean)
-/
@[path]
private lemma ffact_eq_extend (s f : Nat → Int)
  (hf : ∀ k, 0 < k → f k = ∏ d ∈ Nat.divisors k, s d) (t N : Nat) (h : t ≤ N) :
  (∏ i ∈ Finset.Icc 1 t, f i) = ∏ b ∈ Finset.Icc 1 N, s b ^ (t / b) := by
  rw [ffact_eq s f hf t]
  apply Finset.prod_subset (Finset.Icc_subset_Icc_right h)
  intro b hb1 hb2
  simp only [Finset.mem_Icc] at hb1 hb2
  have hbt : t < b := by omega
  have h0 : t / b = 0 := Nat.div_eq_of_lt hbt
  rw [h0, pow_zero]

namespace MetaMathlibExt

/--
[ward_sbinomial_carry_product_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/WardSBinomialCarryProduct.lean)
-/
@[path]
lemma ward_sbinomial_carry_product_general
  {s f : ℕ → ℤ}
  {n m : ℕ}
-- given
  (hs : ∀ b, 0 < b → s b ≠ 0)
  (hf : ∀ k, 0 < k → f k = ∏ d ∈ Nat.divisors k, s d) :
-- imply
  ((∏ i ∈ Finset.Icc 1 (n + m), f i : ℤ) : ℚ) /
    (((∏ i ∈ Finset.Icc 1 n, f i : ℤ) : ℚ) * ((∏ i ∈ Finset.Icc 1 m, f i : ℤ) : ℚ)) =
    ((wardGeneralizedBinomialCoefficient s n m : ℤ) : ℚ) := by
-- proof
  have hN1 : n ≤ n + m := Nat.le_add_right n m
  have hN2 : m ≤ n + m := Nat.le_add_left m n
  have eN : (∏ i ∈ Finset.Icc 1 (n + m), f i) = ∏ b ∈ Finset.Icc 1 (n + m), s b ^ ((n + m) / b) :=
    ffact_eq s f hf (n + m)
  have e1 : (∏ i ∈ Finset.Icc 1 n, f i) = ∏ b ∈ Finset.Icc 1 (n + m), s b ^ (n / b) :=
    ffact_eq_extend s f hf n (n + m) hN1
  have e2 : (∏ i ∈ Finset.Icc 1 m, f i) = ∏ b ∈ Finset.Icc 1 (n + m), s b ^ (m / b) :=
    ffact_eq_extend s f hf m (n + m) hN2
  have cN : ((∏ i ∈ Finset.Icc 1 (n + m), f i : Int) : ℚ) =
    ∏ b ∈ Finset.Icc 1 (n + m), (s b : ℚ) ^ ((n + m) / b) := by
    rw [eN]; push_cast; rfl
  have c1 : ((∏ i ∈ Finset.Icc 1 n, f i : Int) : ℚ) =
    ∏ b ∈ Finset.Icc 1 (n + m), (s b : ℚ) ^ (n / b) := by
    rw [e1]; push_cast; rfl
  have c2 : ((∏ i ∈ Finset.Icc 1 m, f i : Int) : ℚ) =
    ∏ b ∈ Finset.Icc 1 (n + m), (s b : ℚ) ^ (m / b) := by
    rw [e2]; push_cast; rfl
  rw [cN, c1, c2, wardGeneralizedBinomialCoefficient_eq_prod_Icc, Int.cast_prod]
  simp only [Int.cast_pow]
  have hstep : (∏ b ∈ Finset.Icc 1 (n + m), (s b : ℚ) ^ ((n + m) / b)) /
    ((∏ b ∈ Finset.Icc 1 (n + m), (s b : ℚ) ^ (n / b)) *
      (∏ b ∈ Finset.Icc 1 (n + m), (s b : ℚ) ^ (m / b))) =
    ∏ b ∈ Finset.Icc 1 (n + m), (s b : ℚ) ^ ((n % b + m % b) / b) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro b hb
    simp only [Finset.mem_Icc] at hb
    have hbpos : 0 < b := by omega
    have hsQ : (s b : ℚ) ≠ 0 := by exact_mod_cast hs b hbpos
    have hcarry : (n + m) / b = n / b + m / b + (n % b + m % b) / b := carry_eq n m b hbpos
    have hne1 : (s b : ℚ) ^ (n / b) ≠ 0 := pow_ne_zero _ hsQ
    have hne2 : (s b : ℚ) ^ (m / b) ≠ 0 := pow_ne_zero _ hsQ
    have hne : (s b : ℚ) ^ (n / b) * (s b : ℚ) ^ (m / b) ≠ 0 := mul_ne_zero hne1 hne2
    have h1 : (s b : ℚ) ^ ((n + m) / b) / ((s b : ℚ) ^ (n / b) * (s b : ℚ) ^ (m / b))
      = (s b : ℚ) ^ ((n % b + m % b) / b) := by
      rw [hcarry, pow_add, pow_add, mul_div_cancel_left₀ _ hne]
    exact h1
  rw [hstep]
  symm
  apply Finset.prod_subset (Finset.Icc_subset_Icc_left (by omega : 1 ≤ 2))
  intro b hb1 hb2
  simp only [Finset.mem_Icc] at hb1 hb2
  have hb1' : b = 1 := by omega
  subst hb1'
  simp [Nat.mod_one]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ward_sbinomial_carry_product](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/WardSBinomialCarryProduct.lean)
-/
@[path]
lemma ward_sbinomial_carry_product
  {s f : Nat → Int}
  {n m : Nat}
-- given
  (hs : ∀ b, s b ≠ 0)
  (hf : ∀ k, f k = ∏ d ∈ Nat.divisors k, s d) :
-- imply
  let fFactorial : Nat → Int := by
-- proof
  intro fFactorial
  have h := ward_sbinomial_carry_product_general s (fun b _ => hs b) f (fun k _ => hf k) n m
  rw [wardGeneralizedBinomialCoefficient_eq_prod_Icc] at h
  simpa only [fFactorial, Int.cast_prod, Int.cast_pow] using h

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
