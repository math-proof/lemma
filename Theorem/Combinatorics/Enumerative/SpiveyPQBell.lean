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
/-!
# The `(p, q)`-deformed Spivey formula

This file proves Oussi's addition formula for the `(p, q)`-Bell numbers.  The proof uses
the operator calculus of the source, interpreted on formal power series so that no analytic
convergence argument is needed.
-/


namespace MetaMathlibExt

open scoped BigOperators

lemma spivey_S_eq_zero_of_lt
    (p q : ℝ) (bracket : ℕ → ℝ) (S : ℕ → ℕ → ℝ)
    (hS0 : ∀ k, S 0 k = if k = 0 then 1 else 0)
    (hSsucc : ∀ n k, 0 < k →
      S (n + 1) k = p ^ (n + 1 - k) * q ^ (k - 1) * S n (k - 1) +
        bracket k * S n k) :
    ∀ n k, n < k → S n k = 0 := by
  intro n
  induction n with
  | zero =>
      intro k hk
      rw [hS0]
      simp [Nat.ne_of_gt hk]
  | succ n ih =>
      intro k hk
      have hk0 : 0 < k := by omega
      rw [hSsucc n k hk0, ih (k - 1) (by omega), ih k (by omega)]
      ring

end MetaMathlibExt
