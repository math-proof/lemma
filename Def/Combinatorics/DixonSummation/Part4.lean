/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.DixonSummation.Part3
/-!
Source: Abdelmalek Abdesselam, "An algebraic independence result related to a
conjecture of Dixmier on binary form invariants", arXiv:1903.11147v2,
published in Research in the Mathematical Sciences 6 (2019), article 26.
Factorial conventions: TeX lines 322-349; upsilon_m definition: lines 415-421;
Proposition (Dixon), terminating 3F2 summation: lines 502-512.
-/


namespace MetaMathlibExt

/-- Single summand of `upsilon_3`: `(-1)^k` times the three binomial factors. -/
def dixonSummand (a₁ a₂ a₃ k : ℤ) : ℚ :=
  (-1 : ℚ) ^ k.natAbs * intBinom (2 * a₁) (a₁ + k) *
    (intBinom (2 * a₂) (a₂ + k) * intBinom (2 * a₃) (a₃ + k))

/-- Faithful finite-support bound: every nonzero summand satisfies `|k| ≤ bound`. -/
def dixonBound (a₁ a₂ a₃ : ℤ) : ℤ :=
  max (|a₁|) (max (|a₂|) (|a₃|))

/-- `upsilon_3`: finite-support alternating sum over all integers `k`. -/
def upsilon₃ (a₁ a₂ a₃ : ℤ) : ℚ :=
  ∑ k ∈ Finset.Icc (-(dixonBound a₁ a₂ a₃)) (dixonBound a₁ a₂ a₃),
    dixonSummand a₁ a₂ a₃ k

end MetaMathlibExt
