/-
Author: @akiezun, Avocado
-/

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Def.Analysis.SpecialFunctions.Part1Ch5Entry30Secondordereulerian
/-!
# Ramanujan's Notebooks, Part I, Chapter 5, Entry 30

Squarefree and non-squarefree Dirichlet series via ζ(s) and ζ(2s).
-/


namespace Ramanujan.Part1Ch5

namespace Entry30Secondordereulerian

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

/-- The local factor at exponent `0` is `1`. -/
@[simp]
theorem chapter5Entry30LocalCoeff_zero (a : ℕ → ℂ) (p : ℕ) :
    chapter5Entry30LocalCoeff a p 0 = 1 :=
  rfl

/-- The local factor at exponent `1` is `a p`. -/
@[simp]
theorem chapter5Entry30LocalCoeff_one (a : ℕ → ℂ) (p : ℕ) :
    chapter5Entry30LocalCoeff a p 1 = a p :=
  rfl

/-- The local factor vanishes at exponents `e ≥ 2`. -/
theorem chapter5Entry30LocalCoeff_of_two_le (a : ℕ → ℂ) (p e : ℕ) (he : 2 ≤ e) :
    chapter5Entry30LocalCoeff a p e = 0 := by
  have heq : e = (e - 2) + 2 := by omega
  rw [heq]
  rfl

/-- At a squarefree `n ≠ 0`, the coefficient is the product of `a p` over the prime factors
of `n`. -/
theorem chapter5Entry30Coeff_of_squarefree (a : ℕ → ℂ) (n : ℕ) (hn : n ≠ 0) (hsq : Squarefree n) :
    chapter5Entry30Coeff a n = ∏ p ∈ n.primeFactors, a p := by
  unfold chapter5Entry30Coeff
  simp only [hn, ↓reduceIte]
  apply Finset.prod_congr rfl
  intro p hp
  have hpos : 0 < n.factorization p := by
    have hmem2 : p ∈ n.factorization.support := by
      rw [Nat.support_factorization]; exact hp
    have hne := Finsupp.mem_support_iff.mp hmem2
    omega
  have hle : n.factorization p ≤ 1 :=
    (Nat.squarefree_iff_factorization_le_one hn).mp hsq p
  have heq : n.factorization p = 1 := by omega
  change chapter5Entry30LocalCoeff a p (n.factorization p) = a p
  rw [heq]
  rfl

/-- The coefficient vanishes at every non-squarefree `n`. -/
theorem chapter5Entry30Coeff_of_not_squarefree (a : ℕ → ℂ) (n : ℕ) (hn : n ≠ 0)
    (hsq : ¬Squarefree n) : chapter5Entry30Coeff a n = 0 := by
  unfold chapter5Entry30Coeff
  simp only [hn, ↓reduceIte]
  have hle : ¬ ∀ p, n.factorization p ≤ 1 :=
    fun h => hsq ((Nat.squarefree_iff_factorization_le_one hn).mpr h)
  push Not at hle
  obtain ⟨p, hp⟩ := hle
  have hge : 2 ≤ n.factorization p := by omega
  have hzero : chapter5Entry30LocalCoeff a p (n.factorization p) = 0 :=
    chapter5Entry30LocalCoeff_of_two_le a p _ hge
  have hmem : p ∈ n.primeFactors := by
    have hne : n.factorization p ≠ 0 := by omega
    have hmem : p ∈ n.factorization.support := Finsupp.mem_support_iff.mpr hne
    rw [Nat.support_factorization] at hmem
    exact hmem
  exact Finset.prod_eq_zero hmem hzero

/-- For `n ≠ 0`, the coefficient is the product of `a p` over the prime factors of `n` when `n`
is squarefree, and `0` otherwise. -/
theorem chapter5Entry30Coeff_of_ne_zero (a : ℕ → ℂ) (n : ℕ) (hn : n ≠ 0) :
    chapter5Entry30Coeff a n =
      if Squarefree n then ∏ p ∈ n.primeFactors, a p else 0 := by
  split_ifs with hsq
  · exact chapter5Entry30Coeff_of_squarefree a n hn hsq
  · exact chapter5Entry30Coeff_of_not_squarefree a n hn hsq

theorem e30_rpow_prod (s : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) (z : ℝ) :
    Real.rpow (∏ i ∈ s, f i) z = ∏ i ∈ s, Real.rpow (f i) z := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s has ih =>
    have ha : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
    have hs : 0 ≤ ∏ i ∈ s, f i :=
      Finset.prod_nonneg (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have hsub : ∀ i ∈ s, 0 ≤ f i :=
      fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hmul : Real.rpow (f a * ∏ i ∈ s, f i) z
        = Real.rpow (f a) z * Real.rpow (∏ i ∈ s, f i) z := by
      simpa using Real.mul_rpow ha hs (z := z)
    rw [Finset.prod_insert has, Finset.prod_insert has, hmul, ih hsub]

theorem e30_coeff_norm_le (a : ℕ → ℂ) (c : ℝ)
    (ha : ∀ p : ℕ, p.Prime → ‖a p‖ ≤ Real.rpow (p : ℝ) (-c))
    (n : ℕ) (hn : n ≠ 0) :
    ‖chapter5Entry30Coeff a n‖ ≤ Real.rpow (n : ℝ) (-c) := by
  by_cases hsq : Squarefree n
  · rw [chapter5Entry30Coeff_of_squarefree a n hn hsq]
    have hprod : ∏ p ∈ n.primeFactors, p = n :=
      Nat.prod_primeFactors_of_squarefree hsq
    have hcast : ((∏ p ∈ n.primeFactors, p : ℕ) : ℝ)
        = ∏ p ∈ n.primeFactors, (p : ℝ) := Nat.cast_prod _ _
    have hrpow : Real.rpow (∏ p ∈ n.primeFactors, (p : ℝ)) (-c)
        = ∏ p ∈ n.primeFactors, Real.rpow (p : ℝ) (-c) :=
      e30_rpow_prod _ _ (fun i _ => Nat.cast_nonneg _) _
    calc ‖∏ p ∈ n.primeFactors, a p‖
        ≤ ∏ p ∈ n.primeFactors, ‖a p‖ := Finset.norm_prod_le _ _
      _ ≤ ∏ p ∈ n.primeFactors, Real.rpow (p : ℝ) (-c) := by
          apply Finset.prod_le_prod₀
          · intro i hi; exact norm_nonneg _
          · intro i hi
            exact ha i (Nat.mem_primeFactors.mp hi).1
      _ = Real.rpow (n : ℝ) (-c) := by
          rw [← hrpow, ← hcast, hprod]
  · rw [chapter5Entry30Coeff_of_not_squarefree a n hn hsq, norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem e30_summable_rpow {c : ℝ} (hc : 1 < c) :
    Summable (fun n : ℕ => Real.rpow (n : ℝ) (-c)) := by
  have h : Summable (fun n : ℕ => ((n : ℝ) ^ c)⁻¹) :=
    (Real.summable_nat_rpow_inv (p := c)).mpr hc
  refine Summable.congr h (fun n => ?_)
  rw [← Real.rpow_neg (Nat.cast_nonneg n)]
  rfl

theorem e30_summable_shift_two {c : ℝ} (hc : 1 < c) :
    Summable (fun j : ℕ => Real.rpow ((j + 2 : ℕ) : ℝ) (-c)) := by
  have h := e30_summable_rpow hc
  have h2 := (summable_nat_add_iff (G := ℝ) 2).mpr h
  simpa using h2

/-- The coefficients from `n = 2` on are summable when `‖a p‖ ≤ p ^ (-c)` at every prime, for
some `c > 1`. -/
theorem summable_chapter5Entry30Coeff_add_two (a : ℕ → ℂ) (c : ℝ) (hc : 1 < c)
    (ha : ∀ p : ℕ, p.Prime → ‖a p‖ ≤ Real.rpow (p : ℝ) (-c)) :
    Summable (fun j : ℕ => chapter5Entry30Coeff a (j + 2)) := by
  apply Summable.of_norm_bounded (e30_summable_shift_two hc)
  intro j
  have hn : (j + 2) ≠ 0 := by omega
  have h := e30_coeff_norm_le a c ha (j + 2) hn
  simpa using h

/-- The coefficient at `0` is `0`. -/
@[simp]
theorem chapter5Entry30Coeff_zero (a : ℕ → ℂ) : chapter5Entry30Coeff a 0 = 0 := by
  unfold chapter5Entry30Coeff
  simp

/-- The coefficient at `1` is `1`. -/
@[simp]
theorem chapter5Entry30Coeff_one (a : ℕ → ℂ) : chapter5Entry30Coeff a 1 = 1 := by
  unfold chapter5Entry30Coeff
  simp

/-- At a prime `p`, the coefficient is `a p`. -/
theorem chapter5Entry30Coeff_prime (a : ℕ → ℂ) (p : ℕ) (hp : p.Prime) :
    chapter5Entry30Coeff a p = a p := by
  have hn : p ≠ 0 := hp.ne_zero
  have hsq : Squarefree p := hp.prime.squarefree
  rw [chapter5Entry30Coeff_of_squarefree a p hn hsq]
  have hpf : p.primeFactors = {p} := by
    have h1 : (p ^ 1).primeFactors = {p} :=
      Nat.primeFactors_prime_pow one_ne_zero hp
    simpa using h1
  rw [hpf]
  simp

/-- The coefficient vanishes at prime powers `p ^ e` with `e ≥ 2`. -/
theorem chapter5Entry30Coeff_prime_pow_of_two_le (a : ℕ → ℂ) (p e : ℕ) (hp : p.Prime) (he : 2 ≤ e) :
    chapter5Entry30Coeff a (p ^ e) = 0 := by
  have hne : (p ^ e) ≠ 0 := pow_ne_zero e hp.ne_zero
  have hnsq : ¬Squarefree (p ^ e) := by
    intro hsq
    have hle := (Nat.squarefree_iff_factorization_le_one hne).mp hsq p
    have hfact : (p ^ e).factorization p = e := by
      rw [Nat.factorization_pow]
      simp [hp.factorization_self]
    omega
  exact chapter5Entry30Coeff_of_not_squarefree a _ hne hnsq

/-- The coefficient is multiplicative on coprime arguments. -/
theorem chapter5Entry30Coeff_mul_of_coprime (a : ℕ → ℂ) (m n : ℕ) (hcop : Nat.Coprime m n) :
    chapter5Entry30Coeff a (m * n) = chapter5Entry30Coeff a m * chapter5Entry30Coeff a n := by
  by_cases hm : m = 0
  · subst hm
    rw [Nat.coprime_zero_left] at hcop
    subst hcop
    simp [chapter5Entry30Coeff_zero, chapter5Entry30Coeff_one]
  · by_cases hn : n = 0
    · subst hn
      rw [Nat.coprime_zero_right] at hcop
      subst hcop
      simp [chapter5Entry30Coeff_zero, chapter5Entry30Coeff_one]
    · have hmn : m * n ≠ 0 := mul_ne_zero hm hn
      by_cases hsq : Squarefree (m * n)
      · have hsqm : Squarefree m := Squarefree.of_mul_left hsq
        have hsqn : Squarefree n := Squarefree.of_mul_right hsq
        rw [chapter5Entry30Coeff_of_squarefree a _ hmn hsq,
          chapter5Entry30Coeff_of_squarefree a m hm hsqm,
          chapter5Entry30Coeff_of_squarefree a n hn hsqn]
        rw [Nat.primeFactors_mul hm hn]
        rw [Finset.prod_union (Nat.Coprime.disjoint_primeFactors hcop)]
      · have h : ¬(Squarefree m ∧ Squarefree n) := by
          intro ⟨hsm, hsn⟩
          apply hsq
          rw [Nat.squarefree_mul_iff]
          exact ⟨hcop, hsm, hsn⟩
        by_cases hsm : Squarefree m
        · have hsn : ¬Squarefree n := fun hs => h ⟨hsm, hs⟩
          rw [chapter5Entry30Coeff_of_not_squarefree a _ hmn hsq,
            chapter5Entry30Coeff_of_not_squarefree a n hn hsn]
          simp
        · rw [chapter5Entry30Coeff_of_not_squarefree a _ hmn hsq,
            chapter5Entry30Coeff_of_not_squarefree a m hm hsm]
          simp

theorem e30_norm_summable (a : ℕ → ℂ) (c : ℝ) (hc : 1 < c)
    (ha : ∀ p : ℕ, p.Prime → ‖a p‖ ≤ Real.rpow (p : ℝ) (-c)) :
    Summable (fun n : ℕ => ‖chapter5Entry30Coeff a n‖) := by
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ (e30_summable_rpow hc)
  intro n
  by_cases hn : n = 0
  · subst hn
    rw [chapter5Entry30Coeff_zero, norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · exact e30_coeff_norm_le a c ha n hn

theorem e30_tsum_coeff_eq (a : ℕ → ℂ) (c : ℝ) (hc : 1 < c)
    (ha : ∀ p : ℕ, p.Prime → ‖a p‖ ≤ Real.rpow (p : ℝ) (-c)) :
    (∑' n : ℕ, chapter5Entry30Coeff a n) = 1 + ∑' j : ℕ, chapter5Entry30Coeff a (j + 2) := by
  have hsumm : Summable (chapter5Entry30Coeff a) :=
    (e30_norm_summable a c hc ha).of_norm
  have hshift1 := hsumm.tsum_eq_zero_add
  have g_summ : Summable (fun n : ℕ => chapter5Entry30Coeff a (n + 1)) :=
    (summable_nat_add_iff (G := ℂ) 1).mpr hsumm
  have hshift2 := g_summ.tsum_eq_zero_add
  have h0 : chapter5Entry30Coeff a 0 = 0 := chapter5Entry30Coeff_zero a
  have h1 : chapter5Entry30Coeff a (0 + 1) = 1 := by
    have : (0 + 1 : ℕ) = 1 := rfl
    rw [this]
    exact chapter5Entry30Coeff_one a
  have htail : (fun n : ℕ => chapter5Entry30Coeff a ((n + 1) + 1))
      = (fun j : ℕ => chapter5Entry30Coeff a (j + 2)) := by
    funext n
    have heq : (n + 1) + 1 = n + 2 := by omega
    rw [heq]
  rw [h0] at hshift1
  rw [h1] at hshift2
  rw [htail] at hshift2
  have hmid : (∑' b : ℕ, chapter5Entry30Coeff a (b + 1))
      = 1 + ∑' j : ℕ, chapter5Entry30Coeff a (j + 2) := hshift2
  rw [hmid] at hshift1
  simpa using hshift1

theorem e30_tsum_prime_pow (a : ℕ → ℂ) (c : ℝ) (hc : 1 < c)
    (ha : ∀ p : ℕ, p.Prime → ‖a p‖ ≤ Real.rpow (p : ℝ) (-c))
    (p : ℕ) (hp : p.Prime) :
    (∑' e : ℕ, chapter5Entry30Coeff a (p ^ e)) = 1 + a p := by
  have hsumm_all : Summable (chapter5Entry30Coeff a) :=
    (e30_norm_summable a c hc ha).of_norm
  have hp2 : 2 ≤ p := hp.two_le
  have hinj : Function.Injective (fun e : ℕ => p ^ e) := Nat.pow_right_injective hp2
  have hsumm : Summable (fun e : ℕ => chapter5Entry30Coeff a (p ^ e)) :=
    hsumm_all.comp_injective hinj
  have hvanish : ∀ e : ℕ, e ∉ ({0, 1} : Finset ℕ) →
      chapter5Entry30Coeff a (p ^ e) = 0 := by
    intro e he
    have he01 : e ≠ 0 ∧ e ≠ 1 := by
      simpa using he
    have he2 : 2 ≤ e := by omega
    exact chapter5Entry30Coeff_prime_pow_of_two_le a p e hp he2
  have hHasSum : HasSum (fun e : ℕ => chapter5Entry30Coeff a (p ^ e))
      (∑ e ∈ ({0, 1} : Finset ℕ), chapter5Entry30Coeff a (p ^ e)) :=
    hasSum_sum_of_ne_finset_zero hvanish
  have hsum_eq : (∑ e ∈ ({0, 1} : Finset ℕ), chapter5Entry30Coeff a (p ^ e))
      = 1 + a p := by
    rw [Finset.sum_pair (by decide)]
    have e0 : p ^ (0 : ℕ) = 1 := pow_zero p
    have e1 : p ^ (1 : ℕ) = p := pow_one p
    rw [e0, e1, chapter5Entry30Coeff_one, chapter5Entry30Coeff_prime a p hp]
  rw [hsum_eq] at hHasSum
  exact HasSum.unique hsumm.hasSum hHasSum

/-- Euler product: when `‖a p‖ ≤ p ^ (-c)` at every prime, for some `c > 1`, the product of
`1 + a p` over the primes is `1 + ∑' j, chapter5Entry30Coeff a (j + 2)`. -/
theorem hasProd_one_add_chapter5Entry30Coeff (a : ℕ → ℂ) (c : ℝ) (hc : 1 < c)
    (ha : ∀ p : ℕ, p.Prime → ‖a p‖ ≤ Real.rpow (p : ℝ) (-c)) :
    HasProd (fun p : Nat.Primes => 1 + a p)
      (1 + ∑' j : ℕ, chapter5Entry30Coeff a (j + 2)) := by
  have hnorm_summ := e30_norm_summable a c hc ha
  have hsumm_all : Summable (chapter5Entry30Coeff a) := hnorm_summ.of_norm
  have hmult : ∀ {m n : ℕ}, Nat.Coprime m n →
      chapter5Entry30Coeff a (m * n) =
        chapter5Entry30Coeff a m * chapter5Entry30Coeff a n :=
    fun {m n} h => chapter5Entry30Coeff_mul_of_coprime a m n h
  have hEP := EulerProduct.eulerProduct_hasProd (f := chapter5Entry30Coeff a)
    (chapter5Entry30Coeff_one a) hmult hnorm_summ (chapter5Entry30Coeff_zero a)
  have hfac : ∀ q : Nat.Primes,
      (∑' e : ℕ, chapter5Entry30Coeff a (((q : ℕ)) ^ e)) = 1 + a ((q : ℕ)) :=
    fun q => e30_tsum_prime_pow a c hc ha _ q.property
  have htsum := e30_tsum_coeff_eq a c hc ha
  have hEP2 := HasProd.congr_fun hEP (fun q => (hfac q).symm)
  rw [htsum] at hEP2
  exact hEP2

theorem e30_part1 (a : ℕ → ℂ) (c : ℝ) (hc : 1 < c)
    (ha : ∀ p : ℕ, p.Prime → ‖a p‖ ≤ Real.rpow (p : ℝ) (-c)) :
    Summable (fun j : ℕ => chapter5Entry30Coeff a (j + 2)) ∧
      (∀ n : ℕ, n ≠ 0 →
        chapter5Entry30Coeff a n =
          if Squarefree n then ∏ p ∈ n.primeFactors, a p else 0) ∧
      HasProd (fun p : Nat.Primes => 1 + a p)
        (1 + ∑' j : ℕ, chapter5Entry30Coeff a (j + 2)) :=
  ⟨summable_chapter5Entry30Coeff_add_two a c hc ha, chapter5Entry30Coeff_of_ne_zero a,
    hasProd_one_add_chapter5Entry30Coeff a c hc ha⟩

theorem e30_cpow_nat_mul (m n : ℕ) (z : ℂ) :
    ((((m * n : ℕ))) : ℂ) ^ z = ((m : ℂ)) ^ z * ((n : ℂ)) ^ z := by
  rw [← Complex.ofReal_natCast (m * n), ← Complex.ofReal_natCast m,
    ← Complex.ofReal_natCast n, Nat.cast_mul, Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _) z

theorem e30_norm_cpow_nat (n : ℕ) (s : ℂ) (hs : s.re ≠ 0) :
    ‖((n : ℂ)) ^ (-s)‖ = Real.rpow (n : ℝ) (-s.re) := by
  have hbase : ((n : ℂ)) = (((n : ℝ)) : ℂ) := (Complex.ofReal_natCast n).symm
  rw [hbase]
  have hne : (-s).re ≠ 0 := by
    rw [Complex.neg_re]
    exact neg_ne_zero.mpr hs
  have h := Complex.norm_cpow_eq_rpow_re_of_nonneg (Nat.cast_nonneg n) hne
  simpa using h

theorem e30_one_div_cpow_eq (n : ℕ) (s : ℂ) :
    1 / ((n : ℂ) ^ s) = ((n : ℂ) ^ (-s)) := by
  rw [one_div, ← Complex.cpow_neg]

theorem e30_cpow_one (s : ℂ) : ((1 : ℕ) : ℂ) ^ (-s) = 1 := by
  simp

end
end Entry30Secondordereulerian
end Ramanujan.Part1Ch5
