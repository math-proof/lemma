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
import Theorem.Combinatorics.Enumerative.SpiveyPQBell.Part8
/-!
# The `(p, q)`-deformed Spivey formula

This file proves Oussi's addition formula for the `(p, q)`-Bell numbers.  The proof uses
the operator calculus of the source, interpreted on formal power series so that no analytic
convergence argument is needed.
-/


namespace MetaMathlibExt

open scoped BigOperators

noncomputable def spivey_Rpoly
    (p q : ℝ) (bracket : ℕ → ℝ) (S : ℕ → ℕ → ℝ) (m n : ℕ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
    Polynomial.C ((Nat.choose n j : ℝ) * (p ^ Nat.choose k 2 * S m k) *
      bracket k ^ (n - j) * q ^ (j * k)) *
      Polynomial.X ^ k * spivey_BpolyScale p S j (p ^ (n + m - j))

end MetaMathlibExt
