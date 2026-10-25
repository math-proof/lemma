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
import Def.Combinatorics.DixonSummation.Part3
/-!
Source: Abdelmalek Abdesselam, "An algebraic independence result related to a
conjecture of Dixmier on binary form invariants", arXiv:1903.11147v2,
published in Research in the Mathematical Sciences 6 (2019), article 26.
Factorial conventions: TeX lines 322-349; upsilon_m definition: lines 415-421;
Proposition (Dixon), terminating 3F2 summation: lines 502-512.
-/


namespace MetaMathlibExt

/-- Integer binomial coefficients agree with `Nat.choose` on their natural range. -/
@[simp] theorem intBinom_natCast {n k : ℕ} (hk : k ≤ n) :
    intBinom n k = n.choose k := by
  rw [intBinom, ← Int.ofNat_sub hk]
  simp only [extFact_natCast, invFact_natCast]
  rw [Nat.cast_choose ℚ hk]
  field_simp

/-- Integer binomial coefficients vanish when the lower argument is negative. -/
@[simp] theorem intBinom_of_neg_right {n k : ℤ} (hk : k < 0) : intBinom n k = 0 := by
  simp [intBinom, invFact_of_neg hk]

/-- Integer binomial coefficients vanish when the upper argument is below the lower one. -/
@[simp] theorem intBinom_of_lt {n k : ℤ} (h : n < k) : intBinom n k = 0 := by
  simp [intBinom, invFact_of_neg (show n - k < 0 by omega)]

end MetaMathlibExt
