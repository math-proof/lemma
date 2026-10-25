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
import Def.Combinatorics.Enumerative.SpiveyPQBell.Part3
/-!
# The `(p, q)`-deformed Spivey formula

This file proves Oussi's addition formula for the `(p, q)`-Bell numbers.  The proof uses
the operator calculus of the source, interpreted on formal power series so that no analytic
convergence argument is needed.
-/


namespace MetaMathlibExt

open scoped BigOperators

lemma spivey_coeff_Dop (bracket : ℕ → ℝ) (f : PowerSeries ℝ) (i : ℕ) :
    PowerSeries.coeff i (spivey_Dop bracket f) =
      bracket (i + 1) * PowerSeries.coeff (i + 1) f := by
  simp [spivey_Dop, PowerSeries.coeff_mk]

lemma spivey_Dop_Nop_pow (bracket : ℕ → ℝ) (p : ℝ) (a : ℕ) :
    spivey_Dop bracket * (spivey_Nop p) ^ a =
      p ^ a • ((spivey_Nop p) ^ a * spivey_Dop bracket) := by
  apply LinearMap.ext
  intro f
  apply PowerSeries.ext
  intro i
  simp only [Module.End.mul_apply, LinearMap.smul_apply, spivey_coeff_Dop,
    spivey_Nop_pow_apply, PowerSeries.coeff_rescale, PowerSeries.coeff_smul]
  change bracket (i + 1) * ((p ^ a) ^ (i + 1) * PowerSeries.coeff (i + 1) f) =
    p ^ a * ((p ^ a) ^ i * (bracket (i + 1) * PowerSeries.coeff (i + 1) f))
  rw [pow_succ]
  ring

lemma spivey_coeff_XDop (bracket : ℕ → ℝ) (hbracket0 : bracket 0 = 0)
    (f : PowerSeries ℝ) (i : ℕ) :
    PowerSeries.coeff i ((spivey_Xop * spivey_Dop bracket) f) =
      bracket i * PowerSeries.coeff i f := by
  rw [Module.End.mul_apply, spivey_Xop_apply, show PowerSeries.X =
    (PowerSeries.X : PowerSeries ℝ) ^ 1 by simp, PowerSeries.coeff_X_pow_mul']
  cases i with
  | zero => simp [hbracket0]
  | succ i => simp [spivey_coeff_Dop]

lemma spivey_Nop_commute_XDop (bracket : ℕ → ℝ) (hbracket0 : bracket 0 = 0)
    (p : ℝ) : Commute (spivey_Nop p) (spivey_Xop * spivey_Dop bracket) := by
  apply LinearMap.ext
  intro f
  apply PowerSeries.ext
  intro i
  change PowerSeries.coeff i
      (spivey_Nop p ((spivey_Xop * spivey_Dop bracket) f)) =
    PowerSeries.coeff i
      ((spivey_Xop * spivey_Dop bracket) (spivey_Nop p f))
  rw [spivey_Nop_apply, PowerSeries.coeff_rescale,
    spivey_coeff_XDop bracket hbracket0,
    spivey_coeff_XDop bracket hbracket0, spivey_Nop_apply,
    PowerSeries.coeff_rescale]
  ring

lemma spivey_XDop_Xop_pow
    (bracket : ℕ → ℝ) (hbracket0 : bracket 0 = 0) (p q : ℝ)
    (hbracketAdd : ∀ k j, bracket (k + j) =
      p ^ j * bracket k + q ^ k * bracket j) (k : ℕ) :
    (spivey_Xop * spivey_Dop bracket) * spivey_Xop ^ k =
      spivey_Xop ^ k *
        (bracket k • spivey_Nop p + q ^ k • (spivey_Xop * spivey_Dop bracket)) := by
  apply LinearMap.ext
  intro f
  apply PowerSeries.ext
  intro i
  change PowerSeries.coeff i
      ((spivey_Xop * spivey_Dop bracket) ((spivey_Xop ^ k) f)) =
    PowerSeries.coeff i ((spivey_Xop ^ k)
      ((bracket k • spivey_Nop p +
        q ^ k • (spivey_Xop * spivey_Dop bracket)) f))
  rw [spivey_coeff_XDop bracket hbracket0, spivey_Xop_pow_apply,
    spivey_Xop_pow_apply, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_X_pow_mul']
  by_cases hki : k ≤ i
  · simp only [hki, ite_true]
    have hi : k + (i - k) = i := by omega
    have hb := hbracketAdd k (i - k)
    rw [hi] at hb
    rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, map_add,
      PowerSeries.coeff_smul, PowerSeries.coeff_smul, spivey_Nop_apply,
      PowerSeries.coeff_rescale, spivey_coeff_XDop bracket hbracket0, hb]
    change (p ^ (i - k) * bracket k + q ^ k * bracket (i - k)) *
        PowerSeries.coeff (i - k) f =
      bracket k * (p ^ (i - k) * PowerSeries.coeff (i - k) f) +
        q ^ k * (bracket (i - k) * PowerSeries.coeff (i - k) f)
    ring
  · simp [hki]

lemma spivey_basis_shift (bracket : ℕ → ℝ) (p : ℝ) (k a : ℕ) :
    spivey_Xop ^ k * (spivey_Xop * spivey_Dop bracket) *
        (spivey_Nop p) ^ a * (spivey_Dop bracket) ^ k =
      p ^ a • (spivey_Xop ^ (k + 1) * (spivey_Nop p) ^ a *
        (spivey_Dop bracket) ^ (k + 1)) := by
  calc
    spivey_Xop ^ k * (spivey_Xop * spivey_Dop bracket) *
          (spivey_Nop p) ^ a * (spivey_Dop bracket) ^ k =
        (spivey_Xop ^ k * spivey_Xop) *
          (spivey_Dop bracket * (spivey_Nop p) ^ a) *
            (spivey_Dop bracket) ^ k := by noncomm_ring
    _ = (spivey_Xop ^ k * spivey_Xop) *
          (p ^ a • ((spivey_Nop p) ^ a * spivey_Dop bracket)) *
            (spivey_Dop bracket) ^ k := by rw [spivey_Dop_Nop_pow]
    _ = p ^ a • (spivey_Xop ^ (k + 1) * (spivey_Nop p) ^ a *
          (spivey_Dop bracket) ^ (k + 1)) := by
      rw [pow_succ spivey_Xop k, pow_succ' (spivey_Dop bracket) k]
      simp only [smul_mul_assoc, mul_smul_comm]
      congr 1

lemma spivey_XDop_mul_basis
    (bracket : ℕ → ℝ) (hbracket0 : bracket 0 = 0) (p q : ℝ)
    (hbracketAdd : ∀ k j, bracket (k + j) =
      p ^ j * bracket k + q ^ k * bracket j) (k a : ℕ) :
    (spivey_Xop * spivey_Dop bracket) *
        (spivey_Xop ^ k * (spivey_Nop p) ^ a * (spivey_Dop bracket) ^ k) =
      bracket k • (spivey_Xop ^ k * (spivey_Nop p) ^ (a + 1) *
        (spivey_Dop bracket) ^ k) +
      (p ^ a * q ^ k) • (spivey_Xop ^ (k + 1) * (spivey_Nop p) ^ a *
        (spivey_Dop bracket) ^ (k + 1)) := by
  calc
    (spivey_Xop * spivey_Dop bracket) *
          (spivey_Xop ^ k * (spivey_Nop p) ^ a * (spivey_Dop bracket) ^ k) =
        ((spivey_Xop * spivey_Dop bracket) * spivey_Xop ^ k) *
          (spivey_Nop p) ^ a * (spivey_Dop bracket) ^ k := by noncomm_ring
    _ = (spivey_Xop ^ k *
          (bracket k • spivey_Nop p +
            q ^ k • (spivey_Xop * spivey_Dop bracket))) *
          (spivey_Nop p) ^ a * (spivey_Dop bracket) ^ k := by
      rw [spivey_XDop_Xop_pow bracket hbracket0 p q hbracketAdd]
    _ = bracket k • (spivey_Xop ^ k * (spivey_Nop p) ^ (a + 1) *
          (spivey_Dop bracket) ^ k) +
        q ^ k • (spivey_Xop ^ k * (spivey_Xop * spivey_Dop bracket) *
          (spivey_Nop p) ^ a * (spivey_Dop bracket) ^ k) := by
      rw [pow_succ' (spivey_Nop p) a]
      simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm]
      congr 1
    _ = bracket k • (spivey_Xop ^ k * (spivey_Nop p) ^ (a + 1) *
          (spivey_Dop bracket) ^ k) +
        q ^ k • (p ^ a • (spivey_Xop ^ (k + 1) * (spivey_Nop p) ^ a *
          (spivey_Dop bracket) ^ (k + 1))) := by rw [spivey_basis_shift]
    _ = bracket k • (spivey_Xop ^ k * (spivey_Nop p) ^ (a + 1) *
          (spivey_Dop bracket) ^ k) +
        (p ^ a * q ^ k) • (spivey_Xop ^ (k + 1) * (spivey_Nop p) ^ a *
          (spivey_Dop bracket) ^ (k + 1)) := by
      rw [smul_smul]
      congr 2
      ring

end MetaMathlibExt
