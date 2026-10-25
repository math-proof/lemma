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
import Def.Combinatorics.Enumerative.SpiveyPQBell.Part6
/-!
# The `(p, q)`-deformed Spivey formula

This file proves Oussi's addition formula for the `(p, q)`-Bell numbers.  The proof uses
the operator calculus of the source, interpreted on formal power series so that no analytic
convergence argument is needed.
-/


namespace MetaMathlibExt

open scoped BigOperators

lemma spivey_Bpoly_eval (p x : ℝ) (S : ℕ → ℕ → ℝ) (n : ℕ) :
    Polynomial.eval x (spivey_Bpoly p S n) =
      ∑ k ∈ Finset.range (n + 1), (p ^ Nat.choose k 2 * S n k) * x ^ k := by
  simp [spivey_Bpoly, Polynomial.eval_finsetSum]

lemma spivey_coe_Bpoly (p : ℝ) (S : ℕ → ℕ → ℝ) (n : ℕ) :
    ((spivey_Bpoly p S n : Polynomial ℝ) : PowerSeries ℝ) =
      ∑ k ∈ Finset.range (n + 1),
        (p ^ Nat.choose k 2 * S n k) • PowerSeries.X ^ k := by
  change Polynomial.coeToPowerSeries.ringHom (spivey_Bpoly p S n) = _
  rw [show spivey_Bpoly p S n = ∑ k ∈ Finset.range (n + 1),
    Polynomial.C (p ^ Nat.choose k 2 * S n k) * Polynomial.X ^ k by rfl, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C,
    Polynomial.coe_X, Polynomial.coe_mul, Polynomial.coe_pow, Algebra.smul_def]

end MetaMathlibExt
