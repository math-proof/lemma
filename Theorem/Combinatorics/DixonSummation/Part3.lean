/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Def.Combinatorics.DixonSummation.Part3

/-!
Source: Abdelmalek Abdesselam, "An algebraic independence result related to a
conjecture of Dixmier on binary form invariants", arXiv:1903.11147v2,
published in Research in the Mathematical Sciences 6 (2019), article 26.
Factorial conventions: TeX lines 322-349; upsilon_m definition: lines 415-421;
Proposition (Dixon), terminating 3F2 summation: lines 502-512.
-/

public section


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
