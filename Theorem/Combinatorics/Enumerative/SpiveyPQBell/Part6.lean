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
import Def.Combinatorics.Enumerative.SpiveyPQBell.Part5
/-!
# The `(p, q)`-deformed Spivey formula

This file proves Oussi's addition formula for the `(p, q)`-Bell numbers.  The proof uses
the operator calculus of the source, interpreted on formal power series so that no analytic
convergence argument is needed.
-/


namespace MetaMathlibExt

open scoped BigOperators

lemma spivey_coeff_E (p : ℝ) (bracket : ℕ → ℝ) (i : ℕ) :
    PowerSeries.coeff i (spivey_E p bracket) = spivey_ecoeff p bracket i := by
  simp [spivey_E, PowerSeries.coeff_mk]

lemma spivey_ecoeff_succ (p : ℝ) (bracket : ℕ → ℝ)
    (hbracket_ne : ∀ i, 0 < i → bracket i ≠ 0) (i : ℕ) :
    bracket (i + 1) * spivey_ecoeff p bracket (i + 1) =
      p ^ i * spivey_ecoeff p bracket i := by
  simp only [spivey_ecoeff]
  field_simp [hbracket_ne (i + 1) (by omega)]

lemma spivey_Dop_E (p : ℝ) (bracket : ℕ → ℝ)
    (hbracket_ne : ∀ i, 0 < i → bracket i ≠ 0) :
    spivey_Dop bracket (spivey_E p bracket) =
      spivey_Nop p (spivey_E p bracket) := by
  apply PowerSeries.ext
  intro i
  rw [spivey_coeff_Dop, spivey_coeff_E, spivey_Nop_apply,
    PowerSeries.coeff_rescale, spivey_coeff_E]
  exact spivey_ecoeff_succ p bracket hbracket_ne i

lemma spivey_Dop_pow_E (p : ℝ) (bracket : ℕ → ℝ)
    (hbracket_ne : ∀ i, 0 < i → bracket i ≠ 0) (k : ℕ) :
    ((spivey_Dop bracket) ^ k) (spivey_E p bracket) =
      p ^ Nat.choose k 2 • ((spivey_Nop p) ^ k) (spivey_E p bracket) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hDN : spivey_Dop bracket
          (((spivey_Nop p) ^ k) (spivey_E p bracket)) =
          p ^ k • ((spivey_Nop p) ^ k)
            (spivey_Dop bracket (spivey_E p bracket)) := by
        have h := congrArg
          (fun T : Module.End ℝ (PowerSeries ℝ) => T (spivey_E p bracket))
          (spivey_Dop_Nop_pow bracket p k)
        simpa only [Module.End.mul_apply, LinearMap.smul_apply] using h
      have hchoose : Nat.choose (k + 1) 2 = Nat.choose k 2 + k := by
        rw [show 2 = 1 + 1 by rfl, Nat.choose_succ_succ, Nat.choose_one_right]
        exact Nat.add_comm _ _
      calc
        ((spivey_Dop bracket) ^ (k + 1)) (spivey_E p bracket) =
            spivey_Dop bracket
              (((spivey_Dop bracket) ^ k) (spivey_E p bracket)) := by
          rw [pow_succ', Module.End.mul_apply]
        _ = spivey_Dop bracket
              (p ^ Nat.choose k 2 •
                ((spivey_Nop p) ^ k) (spivey_E p bracket)) := by rw [ih]
        _ = p ^ Nat.choose k 2 • spivey_Dop bracket
              (((spivey_Nop p) ^ k) (spivey_E p bracket)) := by rw [map_smul]
        _ = p ^ Nat.choose k 2 •
              (p ^ k • ((spivey_Nop p) ^ k)
                (spivey_Dop bracket (spivey_E p bracket))) := by rw [hDN]
        _ = (p ^ Nat.choose k 2 * p ^ k) •
              ((spivey_Nop p) ^ k)
                (spivey_Nop p (spivey_E p bracket)) := by
          rw [spivey_Dop_E p bracket hbracket_ne, smul_smul]
        _ = p ^ Nat.choose (k + 1) 2 •
              ((spivey_Nop p) ^ (k + 1)) (spivey_E p bracket) := by
          rw [hchoose, pow_add, pow_succ, Module.End.mul_apply]

lemma spivey_Nop_pow_E_ne_zero (p : ℝ) (bracket : ℕ → ℝ) (a : ℕ) :
    ((spivey_Nop p) ^ a) (spivey_E p bracket) ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (PowerSeries.coeff 0) hzero
  rw [spivey_Nop_pow_apply, PowerSeries.coeff_rescale, spivey_coeff_E] at hcoeff
  simp [spivey_ecoeff] at hcoeff

end MetaMathlibExt
