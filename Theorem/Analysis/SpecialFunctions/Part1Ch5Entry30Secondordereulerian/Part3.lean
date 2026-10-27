/-
Author: @akiezun, Avocado
-/

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Def.Analysis.SpecialFunctions.Part1Ch5Entry30Secondordereulerian.Part3
/-!
# Ramanujan's Notebooks, Part I, Chapter 5, Entry 30

Squarefree and non-squarefree Dirichlet series via ζ(s) and ζ(2s).
-/


namespace Ramanujan.Part1Ch5

namespace Entry30Secondordereulerian

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

theorem e30Fmu_zero (s : ℂ) : e30Fmu s 0 = 0 := by
  unfold e30Fmu
  simp

theorem e30_term_mu_eq (s : ℂ) (n : ℕ) :
    LSeries.term (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s n
      = e30Fmu s n := by
  unfold LSeries.term e30Fmu
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, ↓reduceIte]
    rw [div_eq_mul_inv, ← Complex.cpow_neg]

theorem e30_Lmu_tsum (s : ℂ) (hs : 1 < s.re) :
    (∑' n : ℕ, e30Fmu s n) = (riemannZeta s)⁻¹ := by
  have hsumable : LSeriesSummable (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s :=
    (ArithmeticFunction.LSeriesSummable_moebius_iff).mpr hs
  have hHasSum := hsumable.LSeriesHasSum
  have htsum_term : (∑' n : ℕ, LSeries.term _ s n)
      = LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s :=
    HasSum.tsum_eq hHasSum
  have hcongr : (∑' n : ℕ, e30Fmu s n)
      = (∑' n : ℕ, LSeries.term (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s n) :=
    tsum_congr (fun n => (e30_term_mu_eq s n).symm)
  have hprod : LSeries 1 s * LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s = 1 :=
    LSeries_one_mul_Lseries_moebius hs
  have hL1 : LSeries 1 s = riemannZeta s := LSeries_one_eq_riemannZeta hs
  rw [hL1] at hprod
  have hLmu : LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s
      = (riemannZeta s)⁻¹ :=
    eq_inv_of_mul_eq_one_right hprod
  rw [hcongr, htsum_term, hLmu]

theorem e30_summable_Fmu (s : ℂ) (hs : 1 < s.re) : Summable (e30Fmu s) := by
  have hsumable : LSeriesSummable (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s :=
    (ArithmeticFunction.LSeriesSummable_moebius_iff).mpr hs
  exact Summable.congr hsumable (fun n => e30_term_mu_eq s n)

theorem e30_Fmu_shift_tsum (s : ℂ) (hs : 1 < s.re) :
    (∑' j : ℕ, e30Fmu s (j + 1)) = (riemannZeta s)⁻¹ := by
  have hsumm := e30_summable_Fmu s hs
  have hshift := hsumm.tsum_eq_zero_add
  rw [e30Fmu_zero s, zero_add, e30_Lmu_tsum s hs] at hshift
  exact hshift.symm

theorem e30_mu_card (n : ℕ) (hn : n ≠ 0) (hsq : Squarefree n) :
    (((ArithmeticFunction.moebius n : ℤ)) : ℂ) = (-1 : ℂ) ^ (n.primeFactors.card) := by
  have hfact := ArithmeticFunction.IsMultiplicative.multiplicative_factorization
    ArithmeticFunction.moebius ArithmeticFunction.isMultiplicative_moebius hn
  have hsupp : n.factorization.support = n.primeFactors := Nat.support_factorization n
  have hprod : n.factorization.prod (fun p k => ArithmeticFunction.moebius (p ^ k))
      = ∏ p ∈ n.primeFactors, (-1 : ℤ) := by
    have hunfold : n.factorization.prod (fun p k => ArithmeticFunction.moebius (p ^ k))
        = ∏ p ∈ n.factorization.support,
          ArithmeticFunction.moebius (p ^ (n.factorization p)) := rfl
    rw [hunfold, hsupp]
    apply Finset.prod_congr rfl
    intro p hp
    have hpos : 0 < n.factorization p := by
      have hmem2 : p ∈ n.factorization.support := by
        rw [hsupp]; exact hp
      have hne := Finsupp.mem_support_iff.mp hmem2
      omega
    have hle : n.factorization p ≤ 1 :=
      (Nat.squarefree_iff_factorization_le_one hn).mp hsq p
    have heq : n.factorization p = 1 := by omega
    have hprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
    rw [heq, pow_one]
    exact ArithmeticFunction.moebius_apply_prime hprime
  have hmu : ArithmeticFunction.moebius n = ∏ p ∈ n.primeFactors, (-1 : ℤ) := by
    rw [hfact]
    exact hprod
  rw [hmu]
  push_cast
  rw [Finset.prod_const]

/-- Unfolding lemma for `chapter5Entry30OddTerm`. -/
theorem chapter5Entry30OddTerm_def (s : ℂ) (j : ℕ) :
    chapter5Entry30OddTerm s j
      = (if Squarefree (j + 1) ∧ Odd (j + 1).primeFactors.card
        then (((j + 1 : ℕ)) : ℂ) ^ (-s) else 0) := by
  unfold chapter5Entry30OddTerm
  rfl

theorem e30_odd_term_eq (s : ℂ) (j : ℕ) :
    chapter5Entry30OddTerm s j
      = (chapter5Entry30SquarefreeTerm s j - e30Fmu s (j + 1)) / 2 := by
  have hn : (j + 1) ≠ 0 := by omega
  have hmu_t : e30Fmu s (j + 1)
      = ((ArithmeticFunction.moebius (j + 1) : ℤ) : ℂ) * ((((j + 1 : ℕ)) : ℂ) ^ (-s)) := by
    unfold e30Fmu
    simp
  rw [chapter5Entry30OddTerm_def s j, chapter5Entry30SquarefreeTerm_def s j, hmu_t]
  by_cases hsq : Squarefree (j + 1)
  · have hmu := e30_mu_card (j + 1) hn hsq
    by_cases hodd : Odd (j + 1).primeFactors.card
    · have hmu_neg : (((ArithmeticFunction.moebius (j + 1) : ℤ)) : ℂ) = -1 := by
        rw [hmu]
        exact hodd.neg_one_pow
      simp only [hsq, hodd, and_true, ite_true, hmu_neg]
      ring
    · have heven : Even (j + 1).primeFactors.card := Nat.not_odd_iff_even.mp hodd
      have hmu_one : (((ArithmeticFunction.moebius (j + 1) : ℤ)) : ℂ) = 1 := by
        rw [hmu]
        exact heven.neg_one_pow
      simp only [hsq, hodd, and_false, ite_true, ite_false, hmu_one]
      ring
  · have hmu0 : ArithmeticFunction.moebius (j + 1) = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
    have hmu0c : (((ArithmeticFunction.moebius (j + 1) : ℤ)) : ℂ) = 0 := by
      rw [hmu0]
      simp
    simp only [hsq, false_and, ite_false, hmu0c]
    ring

theorem e30_summable_Fmu_shift (s : ℂ) (hs : 1 < s.re) :
    Summable (fun j : ℕ => e30Fmu s (j + 1)) :=
  (summable_nat_add_iff (G := ℂ) 1).mpr (e30_summable_Fmu s hs)

/-- The odd squarefree terms are summable for `1 < s.re`. -/
theorem summable_chapter5Entry30OddTerm (s : ℂ) (hs : 1 < s.re) :
    Summable (chapter5Entry30OddTerm s) := by
  have hRHS : Summable (fun j : ℕ =>
      (chapter5Entry30SquarefreeTerm s j - e30Fmu s (j + 1)) / 2) := by
    have hsub := (summable_chapter5Entry30SquarefreeTerm s hs).sub (e30_summable_Fmu_shift s hs)
    have heq : ∀ j : ℕ, (chapter5Entry30SquarefreeTerm s j - e30Fmu s (j + 1)) / 2
        = (chapter5Entry30SquarefreeTerm s j - e30Fmu s (j + 1)) * (2 : ℂ)⁻¹ := by
      intro j
      rw [div_eq_mul_inv]
    have hmul := hsub.mul_right ((2 : ℂ)⁻¹)
    exact Summable.congr hmul (fun j => (heq j).symm)
  exact Summable.congr hRHS (fun j => (e30_odd_term_eq s j).symm)

theorem e30_odd_tsum (s : ℂ) (hs : 1 < s.re) :
    (∑' j : ℕ, chapter5Entry30OddTerm s j)
      = ((∑' j : ℕ, chapter5Entry30SquarefreeTerm s j)
        - (∑' j : ℕ, e30Fmu s (j + 1))) / 2 := by
  have hsub := (summable_chapter5Entry30SquarefreeTerm s hs).sub (e30_summable_Fmu_shift s hs)
  have htsub : (∑' j : ℕ, (chapter5Entry30SquarefreeTerm s j - e30Fmu s (j + 1)))
      = (∑' j : ℕ, chapter5Entry30SquarefreeTerm s j)
        - (∑' j : ℕ, e30Fmu s (j + 1)) :=
    Summable.tsum_sub (summable_chapter5Entry30SquarefreeTerm s hs) (e30_summable_Fmu_shift s hs)
  have hmul_tsum : (∑' j : ℕ, (chapter5Entry30SquarefreeTerm s j - e30Fmu s (j + 1)) * (2 : ℂ)⁻¹)
      = (∑' j : ℕ, (chapter5Entry30SquarefreeTerm s j - e30Fmu s (j + 1))) * (2 : ℂ)⁻¹ :=
    hsub.tsum_mul_right _
  have hcongr1 : (∑' j : ℕ, chapter5Entry30OddTerm s j)
      = (∑' j : ℕ, (chapter5Entry30SquarefreeTerm s j - e30Fmu s (j + 1)) / 2) :=
    tsum_congr (fun j => e30_odd_term_eq s j)
  have hcongr2 : (fun j : ℕ => (chapter5Entry30SquarefreeTerm s j - e30Fmu s (j + 1)) / 2)
      = (fun j : ℕ => (chapter5Entry30SquarefreeTerm s j - e30Fmu s (j + 1)) * (2 : ℂ)⁻¹) := by
    funext j
    rw [div_eq_mul_inv]
  rw [hcongr1, hcongr2, hmul_tsum, htsub, div_eq_mul_inv]

/-- `∑ n ^ (-s)` over squarefree `n ≥ 1` with an odd number of prime factors is
`(ζ(s) ^ 2 - ζ(2s)) / (2 ζ(s) ζ(2s))` for `1 < s.re`. -/
theorem tsum_chapter5Entry30OddTerm (s : ℂ) (hs : 1 < s.re) :
    (∑' j : ℕ, chapter5Entry30OddTerm s j)
      = (riemannZeta s ^ 2 - riemannZeta (2 * s)) /
        (2 * riemannZeta s * riemannZeta (2 * s)) := by
  have h2re : 1 < (2 * s).re := by
    rw [e30_two_mul_re s]
    linarith
  have hz := riemannZeta_ne_zero_of_one_lt_re hs
  have hz2 := riemannZeta_ne_zero_of_one_lt_re h2re
  rw [e30_odd_tsum s hs, tsum_chapter5Entry30SquarefreeTerm s hs, e30_Fmu_shift_tsum s hs]
  field_simp

theorem e30_summable_cpow (s : ℂ) (hs : 1 < s.re) :
    Summable (fun n : ℕ => (((n : ℕ)) : ℂ) ^ (-s)) := by
  apply Summable.of_norm_bounded (e30_summable_rpow hs)
  intro n
  by_cases hn : n = 0
  · subst hn
    have hcast : ((((0 : ℕ))) : ℂ) = (0 : ℂ) := Nat.cast_zero
    have hns : (-s) ≠ 0 := by
      intro hcon
      have hre : (-s).re = 0 := by rw [hcon]; rfl
      rw [Complex.neg_re] at hre
      have hsne : s.re ≠ 0 := by
        intro hcon2; linarith
      exact hsne (by linarith)
    have h0 : ((((0 : ℕ))) : ℂ) ^ (-s) = 0 := by
      rw [hcast, Complex.zero_cpow hns]
    rw [h0, norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · have hsne : s.re ≠ 0 := by
      intro hcon; linarith
    rw [e30_norm_cpow_nat n s hsne]

theorem e30_cpow_shift_tsum (s : ℂ) (hs : 1 < s.re) :
    (∑' j : ℕ, ((((j + 1 : ℕ)) : ℂ) ^ (-s))) = riemannZeta s := by
  have hz : riemannZeta s = ∑' n : ℕ, 1 / ((n : ℕ) : ℂ) ^ s :=
    zeta_eq_tsum_one_div_nat_cpow hs
  have hcongr : (∑' n : ℕ, 1 / ((n : ℕ) : ℂ) ^ s)
      = (∑' n : ℕ, (((n : ℕ)) : ℂ) ^ (-s)) :=
    tsum_congr (fun n => e30_one_div_cpow_eq n s)
  have hsumm := e30_summable_cpow s hs
  have hshift := hsumm.tsum_eq_zero_add
  have hsne : s ≠ 0 := by
    intro hcon
    rw [hcon, Complex.zero_re] at hs
    linarith
  have hns : (-s) ≠ 0 := neg_ne_zero.mpr hsne
  have h0 : ((((0 : ℕ))) : ℂ) ^ (-s) = 0 := by
    rw [Nat.cast_zero, Complex.zero_cpow hns]
  rw [h0, zero_add] at hshift
  rw [hz, hcongr] at *
  exact hshift.symm

/-- Unfolding lemma for `chapter5Entry30NonSquarefreeTerm`. -/
theorem chapter5Entry30NonSquarefreeTerm_def (s : ℂ) (j : ℕ) :
    chapter5Entry30NonSquarefreeTerm s j
      = (if Squarefree (j + 1) then 0 else ((((j + 1 : ℕ))) : ℂ) ^ (-s)) := by
  unfold chapter5Entry30NonSquarefreeTerm
  rfl

theorem e30_nsq_term_eq (s : ℂ) (j : ℕ) :
    chapter5Entry30NonSquarefreeTerm s j
      = ((((j + 1 : ℕ))) : ℂ) ^ (-s) - chapter5Entry30SquarefreeTerm s j := by
  rw [chapter5Entry30NonSquarefreeTerm_def s j, chapter5Entry30SquarefreeTerm_def s j]
  by_cases hsq : Squarefree (j + 1)
  · simp only [hsq, ite_true]
    ring
  · simp only [hsq, ite_false]
    ring

/-- The non-squarefree terms are summable for `1 < s.re`. -/
theorem summable_chapter5Entry30NonSquarefreeTerm (s : ℂ) (hs : 1 < s.re) :
    Summable (chapter5Entry30NonSquarefreeTerm s) := by
  have hcpow_shift : Summable (fun j : ℕ => ((((j + 1 : ℕ))) : ℂ) ^ (-s)) := by
    have h := e30_summable_cpow s hs
    have h1 := (summable_nat_add_iff (G := ℂ) 1).mpr h
    simpa using h1
  have hsub := hcpow_shift.sub (summable_chapter5Entry30SquarefreeTerm s hs)
  exact Summable.congr hsub (fun j => (e30_nsq_term_eq s j).symm)

theorem e30_nsq_tsum (s : ℂ) (hs : 1 < s.re) :
    (∑' j : ℕ, chapter5Entry30NonSquarefreeTerm s j)
      = (∑' j : ℕ, ((((j + 1 : ℕ))) : ℂ) ^ (-s))
        - (∑' j : ℕ, chapter5Entry30SquarefreeTerm s j) := by
  have hcpow_shift : Summable (fun j : ℕ => ((((j + 1 : ℕ))) : ℂ) ^ (-s)) := by
    have h := e30_summable_cpow s hs
    have h1 := (summable_nat_add_iff (G := ℂ) 1).mpr h
    simpa using h1
  have hcongr : (∑' j : ℕ, chapter5Entry30NonSquarefreeTerm s j)
      = (∑' j : ℕ, (((((j + 1 : ℕ))) : ℂ) ^ (-s) - chapter5Entry30SquarefreeTerm s j)) :=
    tsum_congr (fun j => e30_nsq_term_eq s j)
  rw [hcongr]
  exact Summable.tsum_sub hcpow_shift (summable_chapter5Entry30SquarefreeTerm s hs)

/-- `∑ n ^ (-s)` over non-squarefree `n ≥ 1` is `ζ(s) (ζ(2s) - 1) / ζ(2s)` for `1 < s.re`. -/
theorem tsum_chapter5Entry30NonSquarefreeTerm (s : ℂ) (hs : 1 < s.re) :
    (∑' j : ℕ, chapter5Entry30NonSquarefreeTerm s j)
      = riemannZeta s * (riemannZeta (2 * s) - 1) / riemannZeta (2 * s) := by
  have h2re : 1 < (2 * s).re := by
    rw [e30_two_mul_re s]
    linarith
  have hz2 := riemannZeta_ne_zero_of_one_lt_re h2re
  rw [e30_nsq_tsum s hs, e30_cpow_shift_tsum s hs, tsum_chapter5Entry30SquarefreeTerm s hs]
  field_simp

theorem e30_cpow_nat_prod (s : Finset ℕ) (f : ℕ → ℕ) (z : ℂ) :
    ((((∏ i ∈ s, f i : ℕ))) : ℂ) ^ z = ∏ i ∈ s, ((((f i : ℕ))) : ℂ) ^ z := by
  induction s using Finset.induction with
  | empty =>
    simp
  | insert a t has ih =>
    rw [Finset.prod_insert has, Finset.prod_insert has]
    have hmul := e30_cpow_nat_mul (f a) (∏ i ∈ t, f i) z
    rw [hmul]
    rw [ih]

/-- For `n ≠ 0`, the signed coefficient is `-n ^ (-s)` or `n ^ (-s)` when `n` is squarefree
with an odd or even number of prime factors, and `0` when `n` is not squarefree. -/
theorem chapter5Entry30SignedCoeff_of_ne_zero (s : ℂ) (n : ℕ) (hn : n ≠ 0) :
    chapter5Entry30SignedCoeff s n =
      if Squarefree n then
        if Odd n.primeFactors.card then -((((n : ℕ))) : ℂ) ^ (-s)
        else ((((n : ℕ))) : ℂ) ^ (-s)
      else 0 := by
  have hchar := chapter5Entry30Coeff_of_ne_zero (fun p : ℕ => -((((p : ℕ))) : ℂ) ^ (-s)) n hn
  unfold chapter5Entry30SignedCoeff
  rw [hchar]
  by_cases hsq : Squarefree n
  · simp only [hsq, ite_true]
    have hprod_cpow : (∏ p ∈ n.primeFactors, ((((p : ℕ))) : ℂ) ^ (-s))
        = ((((n : ℕ))) : ℂ) ^ (-s) := by
      have hprod_nat : ∏ p ∈ n.primeFactors, p = n :=
        Nat.prod_primeFactors_of_squarefree hsq
      have hcpow := e30_cpow_nat_prod n.primeFactors (fun p => p) (-s)
      rw [hprod_nat] at hcpow
      exact hcpow.symm
    rw [Finset.prod_neg, hprod_cpow]
    by_cases hodd : Odd n.primeFactors.card
    · simp [hodd, hodd.neg_one_pow]
    · have heven : Even n.primeFactors.card := Nat.not_odd_iff_even.mp hodd
      simp [hodd, heven.neg_one_pow]
  · simp [hsq]

theorem e30_part2 (s : ℂ) (hs : 1 < s.re) :
    (∀ n : ℕ, n ≠ 0 →
      chapter5Entry30SignedCoeff s n =
        if Squarefree n then
          if Odd n.primeFactors.card then -((((n : ℕ))) : ℂ) ^ (-s)
          else ((((n : ℕ))) : ℂ) ^ (-s)
        else 0) ∧
    riemannZeta s ≠ 0 ∧
    riemannZeta (2 * s) ≠ 0 ∧
    Summable (chapter5Entry30SquarefreeTerm s) ∧
    (∑' j : ℕ, chapter5Entry30SquarefreeTerm s j) =
      riemannZeta s / riemannZeta (2 * s) ∧
    Summable (chapter5Entry30OddTerm s) ∧
    (∑' j : ℕ, chapter5Entry30OddTerm s j) =
      (riemannZeta s ^ 2 - riemannZeta (2 * s)) /
        (2 * riemannZeta s * riemannZeta (2 * s)) ∧
    Summable (chapter5Entry30NonSquarefreeTerm s) ∧
    (∑' j : ℕ, chapter5Entry30NonSquarefreeTerm s j) =
      riemannZeta s * (riemannZeta (2 * s) - 1) /
        riemannZeta (2 * s) := by
  have h2re : 1 < (2 * s).re := by
    rw [e30_two_mul_re s]
    linarith
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hz2 : riemannZeta (2 * s) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re h2re
  refine ⟨fun n hn => chapter5Entry30SignedCoeff_of_ne_zero s n hn, hz, hz2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact summable_chapter5Entry30SquarefreeTerm s hs
  · exact tsum_chapter5Entry30SquarefreeTerm s hs
  · exact summable_chapter5Entry30OddTerm s hs
  · exact tsum_chapter5Entry30OddTerm s hs
  · exact summable_chapter5Entry30NonSquarefreeTerm s hs
  · exact tsum_chapter5Entry30NonSquarefreeTerm s hs

/-- Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 5,
Entry 30, pp. 131–132.
Proves `Wanted` entry `ramanujan_part1_ch5_entry30_secondordereulerian`.
-/
theorem ramanujan_part1_ch5_entry30_secondordereulerian :
    (∀ (a : ℕ → ℂ) (c : ℝ), 1 < c →
      (∀ p : ℕ, p.Prime → ‖a p‖ ≤ Real.rpow (p : ℝ) (-c)) →
        Summable (fun j : ℕ => chapter5Entry30Coeff a (j + 2)) ∧
        (∀ n : ℕ, n ≠ 0 →
          chapter5Entry30Coeff a n =
            if Squarefree n then ∏ p ∈ n.primeFactors, a p else 0) ∧
        HasProd (fun p : Nat.Primes => 1 + a p)
          (1 + ∑' j : ℕ, chapter5Entry30Coeff a (j + 2))) ∧
    (∀ s : ℂ, 1 < s.re →
      (∀ n : ℕ, n ≠ 0 →
        chapter5Entry30SignedCoeff s n =
          if Squarefree n then
            if Odd n.primeFactors.card then -((n : ℂ) ^ (-s))
            else (n : ℂ) ^ (-s)
          else 0) ∧
      riemannZeta s ≠ 0 ∧
      riemannZeta (2 * s) ≠ 0 ∧
      Summable (chapter5Entry30SquarefreeTerm s) ∧
      (∑' j : ℕ, chapter5Entry30SquarefreeTerm s j) =
        riemannZeta s / riemannZeta (2 * s) ∧
      Summable (chapter5Entry30OddTerm s) ∧
      (∑' j : ℕ, chapter5Entry30OddTerm s j) =
        (riemannZeta s ^ 2 - riemannZeta (2 * s)) /
          (2 * riemannZeta s * riemannZeta (2 * s)) ∧
      Summable (chapter5Entry30NonSquarefreeTerm s) ∧
      (∑' j : ℕ, chapter5Entry30NonSquarefreeTerm s j) =
        riemannZeta s * (riemannZeta (2 * s) - 1) /
          riemannZeta (2 * s)) := by
  constructor
  · intro a c hc ha
    exact e30_part1 a c hc ha
  · intro s hs
    exact e30_part2 s hs

end
end Entry30Secondordereulerian
end Ramanujan.Part1Ch5
