/-
Author: @akiezun, Avocado
-/

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Def.Analysis.SpecialFunctions.Part1Ch5Entry30Secondordereulerian.Part2
/-!
# Ramanujan's Notebooks, Part I, Chapter 5, Entry 30

Squarefree and non-squarefree Dirichlet series via ζ(s) and ζ(2s).
-/


namespace Ramanujan.Part1Ch5

namespace Entry30Secondordereulerian

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

theorem e30Fplus_zero (s : ℂ) : e30Fplus s 0 = 0 := by
  unfold e30Fplus
  simp

theorem e30Fplus_one (s : ℂ) : e30Fplus s 1 = 1 := by
  unfold e30Fplus
  simp

theorem e30Fplus_mult (s : ℂ) (m n : ℕ) (hcop : Nat.Coprime m n) :
    e30Fplus s (m * n) = e30Fplus s m * e30Fplus s n := by
  unfold e30Fplus
  by_cases hm : m = 0
  · subst hm
    rw [Nat.coprime_zero_left] at hcop
    subst hcop
    simp
  · by_cases hn : n = 0
    · subst hn
      rw [Nat.coprime_zero_right] at hcop
      subst hcop
      simp
    · have hmn : m * n ≠ 0 := mul_ne_zero hm hn
      simp only [hm, hn, hmn, ↓reduceIte]
      by_cases hsq : Squarefree (m * n)
      · have hsqm : Squarefree m := Squarefree.of_mul_left hsq
        have hsqn : Squarefree n := Squarefree.of_mul_right hsq
        simp only [hsq, hsqm, hsqn, ↓reduceIte]
        exact e30_cpow_nat_mul m n (-s)
      · have h : ¬(Squarefree m ∧ Squarefree n) := by
          intro ⟨hsm, hsn⟩
          apply hsq
          rw [Nat.squarefree_mul_iff]
          exact ⟨hcop, hsm, hsn⟩
        by_cases hsm : Squarefree m
        · have hsn : ¬Squarefree n := fun hs => h ⟨hsm, hs⟩
          simp [hsq, hsn]
        · simp [hsq, hsm]

theorem e30Fplus_norm_le (s : ℂ) (hs : 1 < s.re) (n : ℕ) (hn : n ≠ 0) :
    ‖e30Fplus s n‖ ≤ Real.rpow (n : ℝ) (-s.re) := by
  unfold e30Fplus
  simp only [hn, ↓reduceIte]
  by_cases hsq : Squarefree n
  · simp only [hsq, ↓reduceIte]
    have hsne : s.re ≠ 0 := by
      intro hcon
      linarith
    exact (e30_norm_cpow_nat n s hsne).le
  · simp only [hsq, ↓reduceIte, norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg n) _

theorem e30_summable_Fplus_norm (s : ℂ) (hs : 1 < s.re) :
    Summable (fun n : ℕ => ‖e30Fplus s n‖) := by
  have hbase : Summable (fun n : ℕ => Real.rpow (n : ℝ) (-s.re)) :=
    e30_summable_rpow hs
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ hbase
  intro n
  by_cases hn : n = 0
  · subst hn
    rw [e30Fplus_zero, norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · exact e30Fplus_norm_le s hs n hn

theorem e30Fplus_prime_pow_ge_two (s : ℂ) (p e : ℕ) (hp : p.Prime) (he : 2 ≤ e) :
    e30Fplus s (p ^ e) = 0 := by
  have hne : (p ^ e) ≠ 0 := pow_ne_zero e hp.ne_zero
  have hnsq : ¬Squarefree (p ^ e) := by
    intro hsq
    have hle := (Nat.squarefree_iff_factorization_le_one hne).mp hsq p
    have hfact : (p ^ e).factorization p = e := by
      rw [Nat.factorization_pow]
      simp [hp.factorization_self]
    omega
  unfold e30Fplus
  simp [hnsq]

theorem e30Fplus_prime (s : ℂ) (p : ℕ) (hp : p.Prime) :
    e30Fplus s p = ((p : ℂ) ^ (-s)) := by
  unfold e30Fplus
  have hn : p ≠ 0 := hp.ne_zero
  have hsq : Squarefree p := hp.prime.squarefree
  simp [hn, hsq]

theorem e30_tsum_Fplus_prime_pow (s : ℂ) (hs : 1 < s.re) (p : ℕ) (hp : p.Prime) :
    (∑' e : ℕ, e30Fplus s (p ^ e)) = 1 + ((p : ℂ) ^ (-s)) := by
  have hsumm : Summable (e30Fplus s) := (e30_summable_Fplus_norm s hs).of_norm
  have hp2 : 2 ≤ p := hp.two_le
  have hinj : Function.Injective (fun e : ℕ => p ^ e) := Nat.pow_right_injective hp2
  have hsummc : Summable (fun e : ℕ => e30Fplus s (p ^ e)) :=
    hsumm.comp_injective hinj
  have hvanish : ∀ e : ℕ, e ∉ ({0, 1} : Finset ℕ) →
      e30Fplus s (p ^ e) = 0 := by
    intro e he
    have he01 : e ≠ 0 ∧ e ≠ 1 := by
      simpa using he
    have he2 : 2 ≤ e := by omega
    exact e30Fplus_prime_pow_ge_two s p e hp he2
  have hHasSum : HasSum (fun e : ℕ => e30Fplus s (p ^ e))
      (∑ e ∈ ({0, 1} : Finset ℕ), e30Fplus s (p ^ e)) :=
    hasSum_sum_of_ne_finset_zero hvanish
  have hsum_eq : (∑ e ∈ ({0, 1} : Finset ℕ), e30Fplus s (p ^ e))
      = 1 + ((p : ℂ) ^ (-s)) := by
    rw [Finset.sum_pair (by decide)]
    have e0 : p ^ (0 : ℕ) = 1 := pow_zero p
    have e1 : p ^ (1 : ℕ) = p := pow_one p
    have h0 : e30Fplus s (p ^ (0 : ℕ)) = 1 := by
      rw [e0]; exact e30Fplus_one s
    have h1 : e30Fplus s (p ^ (1 : ℕ)) = ((p : ℂ) ^ (-s)) := by
      rw [e1]; exact e30Fplus_prime s p hp
    change e30Fplus s (p ^ (0 : ℕ)) + e30Fplus s (p ^ (1 : ℕ)) = _
    rw [h0, h1]
  rw [hsum_eq] at hHasSum
  exact HasSum.unique hsummc.hasSum hHasSum

theorem e30_Fplus_shift (s : ℂ) (hs : 1 < s.re) :
    (∑' n : ℕ, e30Fplus s n)
      = ∑' j : ℕ, (if Squarefree (j + 1) then (((j + 1 : ℕ)) : ℂ) ^ (-s) else 0) := by
  have hsumm : Summable (e30Fplus s) := (e30_summable_Fplus_norm s hs).of_norm
  have hshift := hsumm.tsum_eq_zero_add
  have h0 : e30Fplus s 0 = 0 := e30Fplus_zero s
  rw [h0, zero_add] at hshift
  have hpt : ∀ b : ℕ, e30Fplus s (b + 1)
      = (if Squarefree (b + 1) then (((b + 1 : ℕ)) : ℂ) ^ (-s) else 0) := by
    intro b
    unfold e30Fplus
    simp
  rw [hshift]
  exact tsum_congr hpt

theorem e30_two_mul_re (s : ℂ) : (2 * s).re = 2 * s.re := by
  have h2 : (2 : ℂ) * s = s + s := by ring
  rw [h2, Complex.add_re]
  ring

theorem e30_cpow_two_mul (p : ℕ) (s : ℂ) (hp0 : ((p : ℂ)) ≠ 0) :
    ((p : ℂ) ^ (-(2 * s))) = (((p : ℂ) ^ (-s)) ^ 2) := by
  have h2 : (2 : ℂ) * s = s + s := by ring
  have hadd : ((p : ℂ) ^ (-(s + s))) = ((p : ℂ) ^ (-s)) * ((p : ℂ) ^ (-s)) := by
    rw [← Complex.cpow_add _ _ hp0]
    congr 1
    ring
  rw [h2] at *
  rw [hadd, pow_two]

theorem e30_norm_prime_cpow_lt_one (p : ℕ) (hp : p.Prime) (s : ℂ) (hs : 1 < s.re) :
    ‖((p : ℂ) ^ (-s))‖ < 1 := by
  have hsne : s.re ≠ 0 := by
    intro hcon; linarith
  rw [e30_norm_cpow_nat p s hsne]
  have hp1 : (1 : ℝ) < (p : ℝ) := by
    have h2 : 2 ≤ p := hp.two_le
    have hc : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h2
    linarith
  have hneg : -s.re < 0 := by linarith
  exact Real.rpow_lt_one_of_one_lt_of_neg hp1 hneg

theorem e30_Splus_eq (s : ℂ) (hs : 1 < s.re) :
    (∑' n : ℕ, e30Fplus s n) = riemannZeta s / riemannZeta (2 * s) := by
  have h2re : 1 < (2 * s).re := by
    rw [e30_two_mul_re s]
    linarith
  have hz2ne : riemannZeta (2 * s) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re h2re
  have hnorm_summ := e30_summable_Fplus_norm s hs
  have hsumm : Summable (e30Fplus s) := hnorm_summ.of_norm
  have hmult : ∀ {m n : ℕ}, Nat.Coprime m n →
      e30Fplus s (m * n) = e30Fplus s m * e30Fplus s n :=
    fun {m n} h => e30Fplus_mult s m n h
  have hEP := EulerProduct.eulerProduct_hasProd (f := e30Fplus s)
    (e30Fplus_one s) hmult hnorm_summ (e30Fplus_zero s)
  have hfac : ∀ q : Nat.Primes,
      (∑' e : ℕ, e30Fplus s (((q : ℕ)) ^ e)) = 1 + (((q : ℕ) : ℂ) ^ (-s)) :=
    fun q => e30_tsum_Fplus_prime_pow s hs _ q.property
  have hEP2 := HasProd.congr_fun hEP (fun q => (hfac q).symm)
  have hZ := riemannZeta_eulerProduct_hasProd (s := s) hs
  have hZ2 := riemannZeta_eulerProduct_hasProd (s := 2 * s) h2re
  have hMul := hEP2.mul hZ2
  have hpt : ∀ q : Nat.Primes,
      (1 + (((q : ℕ) : ℂ) ^ (-s))) * (1 - (((q : ℕ) : ℂ) ^ (-(2 * s))))⁻¹
        = (1 - (((q : ℕ) : ℂ) ^ (-s)))⁻¹ := by
    intro q
    set pn : ℕ := ((q : ℕ)) with hpn
    have hp : pn.Prime := q.property
    have hp0 : ((pn : ℂ)) ≠ 0 := by
      have hne : pn ≠ 0 := hp.ne_zero
      exact Nat.cast_ne_zero.mpr hne
    set x : ℂ := ((pn : ℂ) ^ (-s)) with hx
    set y : ℂ := ((pn : ℂ) ^ (-(2 * s))) with hy
    have hy_eq : y = x ^ 2 := by
      rw [hy, hx]
      exact e30_cpow_two_mul pn s hp0
    have hnx : ‖x‖ < 1 := e30_norm_prime_cpow_lt_one pn hp s hs
    have hny : ‖y‖ < 1 := by
      have hsne2 : (2 * s).re ≠ 0 := by
        intro hcon
        rw [e30_two_mul_re] at hcon
        have : s.re = 0 := by linarith
        linarith
      have hnormy : ‖y‖ = Real.rpow (pn : ℝ) (-(2 * s).re) := by
        rw [hy]
        exact e30_norm_cpow_nat pn (2 * s) hsne2
      rw [hnormy]
      have hp1 : (1 : ℝ) < (pn : ℝ) := by
        have h2 : 2 ≤ pn := hp.two_le
        have hc : (2 : ℝ) ≤ (pn : ℝ) := by exact_mod_cast h2
        linarith
      have hneg : -(2 * s).re < 0 := by
        have : (2 * s).re = 2 * s.re := e30_two_mul_re s
        linarith
      exact Real.rpow_lt_one_of_one_lt_of_neg hp1 hneg
    have h1x : (1 : ℂ) - x ≠ 0 := by
      intro hcon
      have hx1 : x = 1 := (sub_eq_zero.mp hcon).symm
      have h1 : ‖x‖ = 1 := by rw [hx1, norm_one]
      linarith
    have h1px : (1 : ℂ) + x ≠ 0 := by
      intro hcon
      have hxm1 : x = -1 := by linear_combination hcon
      have h1 : ‖x‖ = 1 := by rw [hxm1, norm_neg, norm_one]
      linarith
    have h1y : (1 : ℂ) - y ≠ 0 := by
      intro hcon
      have hy1 : y = 1 := (sub_eq_zero.mp hcon).symm
      have h1 : ‖y‖ = 1 := by rw [hy1, norm_one]
      linarith
    have hfactor : (1 : ℂ) - y = (1 - x) * (1 + x) := by
      rw [hy_eq]
      ring
    rw [hfactor, mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ h1px, one_mul]
  have hMul2 := HasProd.congr_fun hMul (fun q => (hpt q).symm)
  have hEq : (∑' n : ℕ, e30Fplus s n) * riemannZeta (2 * s) = riemannZeta s :=
    HasProd.unique hMul2 hZ
  exact (eq_div_iff hz2ne).mpr hEq

/-- Unfolding lemma for `chapter5Entry30SquarefreeTerm`. -/
theorem chapter5Entry30SquarefreeTerm_def (s : ℂ) (j : ℕ) :
    chapter5Entry30SquarefreeTerm s j
      = (if Squarefree (j + 1) then (((j + 1 : ℕ)) : ℂ) ^ (-s) else 0) := by
  unfold chapter5Entry30SquarefreeTerm
  simp

theorem e30_summable_shift_one {c : ℝ} (hc : 1 < c) :
    Summable (fun j : ℕ => Real.rpow ((j + 1 : ℕ) : ℝ) (-c)) := by
  have h := e30_summable_rpow hc
  have h1 := (summable_nat_add_iff (G := ℝ) 1).mpr h
  simpa using h1

theorem e30_sq_term_Fplus (s : ℂ) (j : ℕ) :
    chapter5Entry30SquarefreeTerm s j = e30Fplus s (j + 1) := by
  rw [chapter5Entry30SquarefreeTerm_def s j]
  unfold e30Fplus
  simp

/-- The squarefree terms are summable for `1 < s.re`. -/
theorem summable_chapter5Entry30SquarefreeTerm (s : ℂ) (hs : 1 < s.re) :
    Summable (chapter5Entry30SquarefreeTerm s) := by
  have hbound : Summable (fun j : ℕ => Real.rpow ((j + 1 : ℕ) : ℝ) (-s.re)) :=
    e30_summable_shift_one hs
  apply Summable.of_norm_bounded hbound
  intro j
  rw [e30_sq_term_Fplus s j]
  exact e30Fplus_norm_le s hs (j + 1) (by omega)

/-- `∑ n ^ (-s)` over squarefree `n ≥ 1` is `ζ(s) / ζ(2s)` for `1 < s.re`. -/
theorem tsum_chapter5Entry30SquarefreeTerm (s : ℂ) (hs : 1 < s.re) :
    (∑' j : ℕ, chapter5Entry30SquarefreeTerm s j)
      = riemannZeta s / riemannZeta (2 * s) := by
  have h1 : (∑' j : ℕ, chapter5Entry30SquarefreeTerm s j)
      = (∑' j : ℕ, (if Squarefree (j + 1) then (((j + 1 : ℕ)) : ℂ) ^ (-s) else 0)) :=
    tsum_congr (fun j => chapter5Entry30SquarefreeTerm_def s j)
  rw [h1, ← e30_Fplus_shift s hs]
  exact e30_Splus_eq s hs

end
end Entry30Secondordereulerian
end Ramanujan.Part1Ch5
