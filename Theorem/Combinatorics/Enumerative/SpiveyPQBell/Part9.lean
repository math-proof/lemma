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
import Def.Combinatorics.Enumerative.SpiveyPQBell.Part8
/-!
# The `(p, q)`-deformed Spivey formula

This file proves Oussi's addition formula for the `(p, q)`-Bell numbers.  The proof uses
the operator calculus of the source, interpreted on formal power series so that no analytic
convergence argument is needed.
-/


namespace MetaMathlibExt

open scoped BigOperators

lemma spivey_Rpoly_eval_one
    (p q : ℝ) (bracket : ℕ → ℝ) (S : ℕ → ℕ → ℝ) (m n : ℕ) :
    Polynomial.eval 1 (spivey_Rpoly p q bracket S m n) =
      ∑ k ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
        (Nat.choose n j : ℝ) * (p ^ Nat.choose k 2 * S m k) *
          bracket k ^ (n - j) * q ^ (j * k) *
            Polynomial.eval (p ^ (n + m - j)) (spivey_Bpoly p S j) := by
  unfold spivey_Rpoly
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, one_pow,
    spivey_BpolyScale_eval_one]
  ring

lemma spivey_coe_Rpoly
    (p q : ℝ) (bracket : ℕ → ℝ) (S : ℕ → ℕ → ℝ) (m n : ℕ) :
    ((spivey_Rpoly p q bracket S m n : Polynomial ℝ) : PowerSeries ℝ) =
      ∑ k ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
        PowerSeries.C ((Nat.choose n j : ℝ) * (p ^ Nat.choose k 2 * S m k) *
          bracket k ^ (n - j) * q ^ (j * k)) *
            (PowerSeries.X ^ k *
              ((spivey_BpolyScale p S j (p ^ (n + m - j)) : Polynomial ℝ) :
                PowerSeries ℝ)) := by
  change Polynomial.coeToPowerSeries.ringHom (spivey_Rpoly p q bracket S m n) = _
  rw [show spivey_Rpoly p q bracket S m n =
    ∑ k ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
      Polynomial.C ((Nat.choose n j : ℝ) * (p ^ Nat.choose k 2 * S m k) *
        bracket k ^ (n - j) * q ^ (j * k)) *
        Polynomial.X ^ k * spivey_BpolyScale p S j (p ^ (n + m - j)) by rfl,
    map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul, map_mul, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_C, map_pow, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_X,
    Polynomial.coeToPowerSeries.ringHom_apply]
  ring

theorem spivey_generic
    (p q : ℝ) (bracket : ℕ → ℝ) (S : ℕ → ℕ → ℝ)
    (hbracket0 : bracket 0 = 0)
    (hbracketAdd : ∀ k j, bracket (k + j) =
      p ^ j * bracket k + q ^ k * bracket j)
    (hbracket_ne : ∀ i, 0 < i → bracket i ≠ 0)
    (hS0 : ∀ k, S 0 k = if k = 0 then 1 else 0)
    (hSsucc0 : ∀ n, S (n + 1) 0 = 0)
    (hSsucc : ∀ n k, 0 < k →
      S (n + 1) k = p ^ (n + 1 - k) * q ^ (k - 1) * S n (k - 1) +
        bracket k * S n k) (m n : ℕ) :
    Polynomial.eval 1 (spivey_Bpoly p S (n + m)) =
      ∑ k ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
        (Nat.choose n j : ℝ) * (p ^ Nat.choose k 2 * S m k) *
          bracket k ^ (n - j) * q ^ (j * k) *
            Polynomial.eval (p ^ (n + m - j)) (spivey_Bpoly p S j) := by
  let A := spivey_Xop * spivey_Dop bracket
  let E := spivey_E p bracket
  let F := ((spivey_Nop p) ^ (n + m)) E
  have hleft := spivey_bell_action p q bracket S hbracket0 hbracketAdd
    hbracket_ne hS0 hSsucc0 hSsucc (n + m)
  have hmexp := spivey_stirling_expansion p q bracket S hbracket0 hbracketAdd
    hS0 hSsucc0 hSsucc m
  have hprod :
      ((spivey_Bpoly p S (n + m) : Polynomial ℝ) : PowerSeries ℝ) * F =
        ((spivey_Rpoly p q bracket S m n : Polynomial ℝ) : PowerSeries ℝ) * F := by
    calc
      ((spivey_Bpoly p S (n + m) : Polynomial ℝ) : PowerSeries ℝ) * F =
          (A ^ (n + m)) E := hleft.symm
      _ = (A ^ n * A ^ m) E := by rw [pow_add]
      _ = (A ^ n *
          (∑ k ∈ Finset.range (m + 1),
            S m k • spivey_basis p bracket m k)) E := by rw [hmexp]
      _ = (∑ k ∈ Finset.range (m + 1),
          S m k • (A ^ n * spivey_basis p bracket m k)) E := by
        rw [Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        rw [mul_smul_comm]
      _ = ∑ k ∈ Finset.range (m + 1),
          S m k • ((A ^ n * spivey_basis p bracket m k) E) := by
        rw [LinearMap.sum_apply]
        apply Finset.sum_congr rfl
        intro k _
        rw [LinearMap.smul_apply]
      _ = ∑ k ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
          ((Nat.choose n j : ℝ) * (p ^ Nat.choose k 2 * S m k) *
            bracket k ^ (n - j) * q ^ (j * k)) •
              ((PowerSeries.X ^ k *
                  ((spivey_BpolyScale p S j (p ^ (n + m - j)) : Polynomial ℝ) :
                    PowerSeries ℝ)) * F) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkm : k ≤ m := by
          simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hk
        rw [spivey_expand_term_E p q bracket S hbracket0 hbracketAdd
          hbracket_ne hS0 hSsucc0 hSsucc m n k hkm, Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [smul_smul]
        congr 1
        ring
      _ = ((spivey_Rpoly p q bracket S m n : Polynomial ℝ) : PowerSeries ℝ) * F := by
        rw [spivey_coe_Rpoly, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        rw [PowerSeries.smul_eq_C_mul]
        ring
  have hF : F ≠ 0 := spivey_Nop_pow_E_ne_zero p bracket (n + m)
  have hcoe :
      ((spivey_Bpoly p S (n + m) : Polynomial ℝ) : PowerSeries ℝ) =
        ((spivey_Rpoly p q bracket S m n : Polynomial ℝ) : PowerSeries ℝ) :=
    mul_right_cancel₀ hF hprod
  have hpoly : spivey_Bpoly p S (n + m) = spivey_Rpoly p q bracket S m n :=
    Polynomial.coe_injective ℝ hcoe
  have heval := congrArg (Polynomial.eval 1) hpoly
  rw [spivey_Rpoly_eval_one] at heval
  exact heval

theorem spivey_generic_sum
    (p q : ℝ) (bracket : ℕ → ℝ) (S : ℕ → ℕ → ℝ)
    (hbracket0 : bracket 0 = 0)
    (hbracketAdd : ∀ k j, bracket (k + j) = p ^ j * bracket k + q ^ k * bracket j)
    (hbracket_ne : ∀ k, 0 < k → bracket k ≠ 0)
    (hS0 : ∀ k, S 0 k = if k = 0 then 1 else 0)
    (hSsucc0 : ∀ a, S (a + 1) 0 = 0)
    (hSsucc : ∀ a k, 0 < k →
      S (a + 1) k = p ^ (a + 1 - k) * q ^ (k - 1) * S a (k - 1) +
        bracket k * S a k)
    (m n : ℕ) :
    (∑ k ∈ Finset.range (n + m + 1),
        (p ^ Nat.choose k 2 * S (n + m) k) * 1 ^ k) =
      ∑ k ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
        (Nat.choose n j : ℝ) * (p ^ Nat.choose k 2 * S m k) * bracket k ^ (n - j)
          * q ^ (j * k) *
            ∑ ell ∈ Finset.range (j + 1),
              (p ^ Nat.choose ell 2 * S j ell) * (p ^ (n + m - j)) ^ ell := by
  simpa [spivey_Bpoly_eval] using
    spivey_generic p q bracket S hbracket0 hbracketAdd hbracket_ne hS0 hSsucc0 hSsucc m n

end MetaMathlibExt
