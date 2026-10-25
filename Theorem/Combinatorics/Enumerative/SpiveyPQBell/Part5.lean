/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/SpiveyPQBell.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.SpiveyPQBell.Part4
/-!
# The `(p, q)`-deformed Spivey formula

This file proves Oussi's addition formula for the `(p, q)`-Bell numbers.  The proof uses
the operator calculus of the source, interpreted on formal power series so that no analytic
convergence argument is needed.
-/


namespace MetaMathlibExt

open scoped BigOperators

lemma spivey_XDop_mul_basis_of_le
    (bracket : ℕ → ℝ) (hbracket0 : bracket 0 = 0) (p q : ℝ)
    (hbracketAdd : ∀ k j, bracket (k + j) =
      p ^ j * bracket k + q ^ k * bracket j) (n k : ℕ) (hkn : k ≤ n) :
    (spivey_Xop * spivey_Dop bracket) * spivey_basis p bracket n k =
      bracket k • spivey_basis p bracket (n + 1) k +
        (p ^ (n - k) * q ^ k) • spivey_basis p bracket (n + 1) (k + 1) := by
  unfold spivey_basis
  rw [spivey_XDop_mul_basis bracket hbracket0 p q hbracketAdd k (n - k)]
  have h₁ : n - k + 1 = n + 1 - k := by omega
  have h₂ : n + 1 - (k + 1) = n - k := by omega
  rw [h₁, h₂]

lemma spivey_recurrence_sum
    {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (n : ℕ) (S Snext b c : ℕ → ℝ) (T : ℕ → V)
    (hzero : Snext 0 = 0)
    (hrec : ∀ k, Snext (k + 1) = c k * S k + b (k + 1) * S (k + 1))
    (hbzero : b 0 = 0) (htop : S (n + 1) = 0) :
    (∑ k ∈ Finset.range (n + 2), Snext k • T k) =
      ∑ k ∈ Finset.range (n + 1),
        ((c k * S k) • T (k + 1) + (b k * S k) • T k) := by
  have hshift :
      (∑ k ∈ Finset.range (n + 1), (b (k + 1) * S (k + 1)) • T (k + 1)) =
        ∑ k ∈ Finset.range (n + 1), (b k * S k) • T k := by
    let g : ℕ → V := fun k => (b k * S k) • T k
    have hfirst := Finset.sum_range_succ' g (n + 1)
    have hlast := Finset.sum_range_succ g (n + 1)
    have hgzero : g 0 = 0 := by simp [g, hbzero]
    have hgtop : g (n + 1) = 0 := by simp [g, htop]
    rw [hgzero, add_zero] at hfirst
    rw [hgtop, add_zero] at hlast
    change (∑ k ∈ Finset.range (n + 1), g (k + 1)) =
      ∑ k ∈ Finset.range (n + 1), g k
    rw [← hfirst, hlast]
  rw [Finset.sum_range_succ']
  simp only [hzero, zero_smul, add_zero]
  calc
    (∑ k ∈ Finset.range (n + 1), Snext (k + 1) • T (k + 1)) =
        (∑ k ∈ Finset.range (n + 1), (c k * S k) • T (k + 1)) +
          ∑ k ∈ Finset.range (n + 1), (b (k + 1) * S (k + 1)) • T (k + 1) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [hrec, add_smul]
    _ = (∑ k ∈ Finset.range (n + 1), (c k * S k) • T (k + 1)) +
          ∑ k ∈ Finset.range (n + 1), (b k * S k) • T k := by rw [hshift]
    _ = ∑ k ∈ Finset.range (n + 1),
          ((c k * S k) • T (k + 1) + (b k * S k) • T k) := by
      rw [Finset.sum_add_distrib]

theorem spivey_stirling_expansion
    (p q : ℝ) (bracket : ℕ → ℝ) (S : ℕ → ℕ → ℝ)
    (hbracket0 : bracket 0 = 0)
    (hbracketAdd : ∀ k j, bracket (k + j) =
      p ^ j * bracket k + q ^ k * bracket j)
    (hS0 : ∀ k, S 0 k = if k = 0 then 1 else 0)
    (hSsucc0 : ∀ n, S (n + 1) 0 = 0)
    (hSsucc : ∀ n k, 0 < k →
      S (n + 1) k = p ^ (n + 1 - k) * q ^ (k - 1) * S n (k - 1) +
        bracket k * S n k) (n : ℕ) :
    (spivey_Xop * spivey_Dop bracket) ^ n =
      ∑ k ∈ Finset.range (n + 1), S n k • spivey_basis p bracket n k := by
  induction n with
  | zero =>
      simp [hS0, spivey_basis]
  | succ n ih =>
      have htop : S n (n + 1) = 0 :=
        spivey_S_eq_zero_of_lt p q bracket S hS0 hSsucc n (n + 1) (by omega)
      have hrec : ∀ k, S (n + 1) (k + 1) =
          (p ^ (n + 1 - (k + 1)) * q ^ k) * S n k +
            bracket (k + 1) * S n (k + 1) := by
        intro k
        rw [hSsucc n (k + 1) (by omega)]
        simp only [Nat.add_sub_cancel]
      have hcollect := spivey_recurrence_sum n (fun k => S n k)
        (fun k => S (n + 1) k) bracket
        (fun k => p ^ (n + 1 - (k + 1)) * q ^ k)
        (fun k => spivey_basis p bracket (n + 1) k)
        (hSsucc0 n) hrec hbracket0 htop
      rw [pow_succ', ih, Finset.mul_sum]
      calc
        (∑ k ∈ Finset.range (n + 1),
            (spivey_Xop * spivey_Dop bracket) *
              (S n k • spivey_basis p bracket n k)) =
            ∑ k ∈ Finset.range (n + 1),
              (((p ^ (n + 1 - (k + 1)) * q ^ k) * S n k) •
                  spivey_basis p bracket (n + 1) (k + 1) +
                (bracket k * S n k) • spivey_basis p bracket (n + 1) k) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hkn : k ≤ n := by
            simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hk
          have hexp : n + 1 - (k + 1) = n - k := by omega
          rw [mul_smul_comm,
            spivey_XDop_mul_basis_of_le bracket hbracket0 p q hbracketAdd n k hkn,
            smul_add, smul_smul, smul_smul, hexp]
          conv_lhs => rw [add_comm]
          congr 1 <;> ring_nf
        _ = ∑ k ∈ Finset.range (n + 2),
              S (n + 1) k • spivey_basis p bracket (n + 1) k := hcollect.symm

lemma spivey_XDop_pow_Xop_pow
    (bracket : ℕ → ℝ) (hbracket0 : bracket 0 = 0) (p q : ℝ)
    (hbracketAdd : ∀ k j, bracket (k + j) =
      p ^ j * bracket k + q ^ k * bracket j) (n k : ℕ) :
    (spivey_Xop * spivey_Dop bracket) ^ n * spivey_Xop ^ k =
      spivey_Xop ^ k *
        (bracket k • spivey_Nop p +
          q ^ k • (spivey_Xop * spivey_Dop bracket)) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      let A := spivey_Xop * spivey_Dop bracket
      let C := bracket k • spivey_Nop p + q ^ k • A
      calc
        A ^ (n + 1) * spivey_Xop ^ k = A * (A ^ n * spivey_Xop ^ k) := by
          rw [pow_succ']
          noncomm_ring
        _ = A * (spivey_Xop ^ k * C ^ n) := by rw [ih]
        _ = (spivey_Xop ^ k * C) * C ^ n := by
          rw [← mul_assoc, spivey_XDop_Xop_pow bracket hbracket0 p q hbracketAdd]
        _ = spivey_Xop ^ k * C ^ (n + 1) := by
          rw [pow_succ']
          noncomm_ring

lemma spivey_coeff_XDop_pow (bracket : ℕ → ℝ)
    (hbracket0 : bracket 0 = 0) (j : ℕ) (f : PowerSeries ℝ) (i : ℕ) :
    PowerSeries.coeff i (((spivey_Xop * spivey_Dop bracket) ^ j) f) =
      bracket i ^ j * PowerSeries.coeff i f := by
  induction j generalizing f with
  | zero => simp
  | succ j ih =>
      rw [pow_succ, Module.End.mul_apply, ih,
        spivey_coeff_XDop bracket hbracket0, pow_succ]
      ring

lemma spivey_coeff_binomial_base
    (bracket : ℕ → ℝ) (hbracket0 : bracket 0 = 0) (p q : ℝ)
    (hbracketAdd : ∀ k j, bracket (k + j) =
      p ^ j * bracket k + q ^ k * bracket j) (k : ℕ)
    (f : PowerSeries ℝ) (i : ℕ) :
    PowerSeries.coeff i
        ((bracket k • spivey_Nop p +
          q ^ k • (spivey_Xop * spivey_Dop bracket)) f) =
      bracket (k + i) * PowerSeries.coeff i f := by
  rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, map_add,
    PowerSeries.coeff_smul, PowerSeries.coeff_smul, spivey_Nop_apply,
    PowerSeries.coeff_rescale, spivey_coeff_XDop bracket hbracket0,
    hbracketAdd]
  change bracket k * (p ^ i * PowerSeries.coeff i f) +
      q ^ k * (bracket i * PowerSeries.coeff i f) =
    (p ^ i * bracket k + q ^ k * bracket i) * PowerSeries.coeff i f
  ring

lemma spivey_coeff_binomial_base_pow
    (bracket : ℕ → ℝ) (hbracket0 : bracket 0 = 0) (p q : ℝ)
    (hbracketAdd : ∀ k j, bracket (k + j) =
      p ^ j * bracket k + q ^ k * bracket j) (n k : ℕ)
    (f : PowerSeries ℝ) (i : ℕ) :
    PowerSeries.coeff i
        (((bracket k • spivey_Nop p +
          q ^ k • (spivey_Xop * spivey_Dop bracket)) ^ n) f) =
      bracket (k + i) ^ n * PowerSeries.coeff i f := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Module.End.mul_apply, ih,
        spivey_coeff_binomial_base bracket hbracket0 p q hbracketAdd,
        pow_succ]
      ring

lemma spivey_binomial_expansion
    (bracket : ℕ → ℝ) (hbracket0 : bracket 0 = 0) (p q : ℝ)
    (hbracketAdd : ∀ k j, bracket (k + j) =
      p ^ j * bracket k + q ^ k * bracket j) (n k : ℕ) :
    (bracket k • spivey_Nop p +
        q ^ k • (spivey_Xop * spivey_Dop bracket)) ^ n =
      ∑ j ∈ Finset.range (n + 1),
        ((Nat.choose n j : ℝ) * bracket k ^ (n - j) * q ^ (j * k)) •
          ((spivey_Nop p) ^ (n - j) *
            (spivey_Xop * spivey_Dop bracket) ^ j) := by
  apply LinearMap.ext
  intro f
  apply PowerSeries.ext
  intro i
  rw [spivey_coeff_binomial_base_pow bracket hbracket0 p q hbracketAdd,
    LinearMap.sum_apply, map_sum]
  simp only [LinearMap.smul_apply, PowerSeries.coeff_smul, Module.End.mul_apply,
    spivey_Nop_pow_apply, PowerSeries.coeff_rescale,
    spivey_coeff_XDop_pow bracket hbracket0]
  rw [hbracketAdd, add_comm, add_pow, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  simp only [mul_pow]
  rw [← pow_mul, ← pow_mul, ← pow_mul]
  rw [Nat.mul_comm k j, Nat.mul_comm i (n - j)]
  ring

lemma spivey_push_Xop
    (bracket : ℕ → ℝ) (hbracket0 : bracket 0 = 0) (p q : ℝ)
    (hbracketAdd : ∀ k j, bracket (k + j) =
      p ^ j * bracket k + q ^ k * bracket j) (n k : ℕ) :
    (spivey_Xop * spivey_Dop bracket) ^ n * spivey_Xop ^ k =
      spivey_Xop ^ k *
        (∑ j ∈ Finset.range (n + 1),
          ((Nat.choose n j : ℝ) * bracket k ^ (n - j) * q ^ (j * k)) •
            ((spivey_Nop p) ^ (n - j) *
              (spivey_Xop * spivey_Dop bracket) ^ j)) := by
  rw [spivey_XDop_pow_Xop_pow bracket hbracket0 p q hbracketAdd,
    spivey_binomial_expansion bracket hbracket0 p q hbracketAdd]

end MetaMathlibExt
